/* Based on Building LISP (http://www.lwh.jp/lisp/index.html) */
/* with bug fixes and enhancements */
/* case-sensitive Lisp-1 */

#ifdef _MSC_VER
#define _CRT_SECURE_NO_WARNINGS
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>

#ifdef _MSC_VER
#define strdup _strdup
#endif

enum AtomType {
	AtomType_Nil,
	AtomType_Pair,
	AtomType_Symbol,
	AtomType_Integer,
	AtomType_Builtin,
	AtomType_Closure,
	AtomType_Macro
};

typedef enum {
	Error_OK = 0, Error_Syntax, Error_Unbound, Error_Args, Error_Type
} Error;

typedef struct Atom Atom;
typedef Error(*Builtin)(Atom args, Atom *result);

struct Atom {
	enum AtomType type;

	union {		
		long integer;
		struct Pair *pair;
		char *symbol;
		Builtin builtin;
	} value;
};

static Atom sym_table = { AtomType_Nil };

struct Pair {
	struct Atom atom[2];
};

Error apply(Atom fn, Atom args, Atom *result);
int listp(Atom expr);
char *slurp(const char *path);

#define car(p) ((p).value.pair->atom[0])
#define cdr(p) ((p).value.pair->atom[1])
#define nilp(atom) ((atom).type == AtomType_Nil)

static const Atom nil = { AtomType_Nil };
/* symbols for faster comparison */
static Atom sym_t, sym_quote, sym_define, sym_lambda, sym_if, sym_defmacro, sym_and;

struct Allocation {
	struct Pair pair;
	int mark : 1;
	struct Allocation *next;
};

struct Allocation *global_allocations = NULL;

Atom cons(Atom car_val, Atom cdr_val)
{
	struct Allocation *a;
	Atom p;

	a = (struct Allocation *)malloc(sizeof(struct Allocation));
	a->mark = 0;
	a->next = global_allocations;
	global_allocations = a;

	p.type = AtomType_Pair;
	p.value.pair = &a->pair;

	car(p) = car_val;
	cdr(p) = cdr_val;

	return p;
}

void gc_mark(Atom root)
{
	struct Allocation *a;

	if (!(root.type == AtomType_Pair
		|| root.type == AtomType_Closure
		|| root.type == AtomType_Macro))
		return;

	a = (struct Allocation *)
		((char *)root.value.pair
		- offsetof(struct Allocation, pair));

	if (a->mark)
		return;

	a->mark = 1;

	gc_mark(car(root));
	gc_mark(cdr(root));
}

void gc()
{
	struct Allocation *a, **p;
	gc_mark(sym_table);

	/* Free unmarked allocations */
	p = &global_allocations;
	while (*p != NULL) {
		a = *p;
		if (!a->mark) {
			*p = a->next;
			free(a);
		}
		else {
			p = &a->next;
		}
	}

	/* Clear marks */
	a = global_allocations;
	while (a != NULL) {
		a->mark = 0;
		a = a->next;
	}
}


Atom make_int(long x)
{
	Atom a;
	a.type = AtomType_Integer;
	a.value.integer = x;
	return a;
}

Atom make_sym(const char *s)
{
	Atom a, p;

	p = sym_table;
	while (!nilp(p)) {
		a = car(p);
		if (strcmp(a.value.symbol, s) == 0)
			return a;
		p = cdr(p);
	}

	a.type = AtomType_Symbol;
	a.value.symbol = (char*)strdup(s);
	sym_table = cons(a, sym_table);

	return a;
}

Atom make_builtin(Builtin fn)
{
	Atom a;
	a.type = AtomType_Builtin;
	a.value.builtin = fn;
	return a;
}

Error make_closure(Atom env, Atom args, Atom body, Atom *result)
{
	Atom p;

	if (!listp(body))
		return Error_Syntax;

	/* Check argument names are all symbols */
	p = args;
	while (!nilp(p)) {
		if (p.type == AtomType_Symbol)
			break;
		else if (p.type != AtomType_Pair
			|| car(p).type != AtomType_Symbol)
			return Error_Type;
		p = cdr(p);
	}

	*result = cons(env, cons(args, body));
	result->type = AtomType_Closure;

	return Error_OK;
}



void print_expr(Atom atom)
{
	switch (atom.type) {
	case AtomType_Nil:
		printf("nil");
		break;
	case AtomType_Pair:
		putchar('(');
		print_expr(car(atom));
		atom = cdr(atom);
		while (!nilp(atom)) {
			if (atom.type == AtomType_Pair) {
				putchar(' ');
				print_expr(car(atom));
				atom = cdr(atom);
			}
			else {
				printf(" . ");
				print_expr(atom);
				break;
			}
		}
		putchar(')');
		break;
	case AtomType_Symbol:
		printf("%s", atom.value.symbol);
		break;
	case AtomType_Integer:
		printf("%ld", atom.value.integer);
		break;
	case AtomType_Builtin:
		printf("#<BUILTIN:%p>", atom.value.builtin);
		break;
	case AtomType_Closure:
		print_expr(cdr(atom));
		break;
	default:
		printf("unknown type");
		break;
	}
}

Error lex(const char *str, const char **start, const char **end)
{
	const char *ws = " \t\r\n";
	const char *delim = "() \t\r\n";
	const char *prefix = "()'`";

	str += strspn(str, ws);

	if (str[0] == '\0') {
		*start = *end = NULL;
		return Error_Syntax;
	}

	*start = str;

	if (strchr(prefix, str[0]) != NULL)
		*end = str + 1;
	else if (str[0] == ',')
		*end = str + (str[1] == '@' ? 2 : 1);
	else
		*end = str + strcspn(str, delim);

	return Error_OK;
}

Error read_expr(const char *input, const char **end, Atom *result);

Error parse_simple(const char *start, const char *end, Atom *result)
{
	char *buf, *p;

	/* Is it an integer? */
	long val = strtol(start, &p, 10);
	if (p == end) {
		result->type = AtomType_Integer;
		result->value.integer = val;
		return Error_OK;
	}

	/* NIL or symbol */
	buf = (char*)malloc(end - start + 1);
	p = buf;
	while (start != end)
		/* *p++ = toupper(*start), ++start; */
		*p++ = *start, ++start;
	*p = '\0';

	if (strcmp(buf, "nil") == 0)
		*result = nil;
	else
		*result = make_sym(buf);

	free(buf);

	return Error_OK;
}

Error read_list(const char *start, const char **end, Atom *result)
{
	Atom p;

	*end = start;
	p = *result = nil;

	for (;;) {
		const char *token;
		Atom item;
		Error err;

		err = lex(*end, &token, end);
		if (err)
			return err;

		if (token[0] == ')')
			return Error_OK;

		if (token[0] == '.' && *end - token == 1) {
			/* Improper list */
			if (nilp(p))
				return Error_Syntax;

			err = read_expr(*end, end, &item);
			if (err)
				return err;

			cdr(p) = item;

			/* Read the closing ')' */
			err = lex(*end, &token, end);
			if (!err && token[0] != ')')
				err = Error_Syntax;

			return err;
		}

		err = read_expr(token, end, &item);
		if (err)
			return err;

		if (nilp(p)) {
			/* First item */
			*result = cons(item, nil);
			p = *result;
		}
		else {
			cdr(p) = cons(item, nil);
			p = cdr(p);
		}
	}
}

Error read_expr(const char *input, const char **end, Atom *result)
{
	const char *token;
	Error err;

	err = lex(input, &token, end);
	if (err)
		return err;

	if (token[0] == '(')
		return read_list(*end, end, result);
	else if (token[0] == ')')
		return Error_Syntax;
	else if (token[0] == '\'') {
		*result = cons(make_sym("quote"), cons(nil, nil));
		return read_expr(*end, end, &car(cdr(*result)));
	}
	else if (token[0] == '`') {
		*result = cons(make_sym("quasiquote"), cons(nil, nil));
		return read_expr(*end, end, &car(cdr(*result)));
	}
	else if (token[0] == ',') {
		*result = cons(make_sym(
			token[1] == '@' ? "unquote-splicing" : "unquote"),
			cons(nil, nil));
		return read_expr(*end, end, &car(cdr(*result)));
	}
	else
		return parse_simple(token, *end, result);
}

char *readline(char *prompt) {
	char ret[2000]; /* one screenful */
	printf(prompt);
	fgets(ret, sizeof(ret), stdin);
	if (feof(stdin)) return NULL;
	return (char*)strdup(ret);
}

Atom env_create(Atom parent)
{
	return cons(parent, nil);
}

Error env_get(Atom env, Atom symbol, Atom *result)
{
	Atom parent = car(env);
	Atom bs = cdr(env);

	while (!nilp(bs)) {
		Atom b = car(bs);
		if (car(b).value.symbol == symbol.value.symbol) {
			*result = cdr(b);
			return Error_OK;
		}
		bs = cdr(bs);
	}

	if (nilp(parent))
		return Error_Unbound;

	return env_get(parent, symbol, result);
}

Error env_set(Atom env, Atom symbol, Atom value)
{
	Atom bs = cdr(env);
	Atom b = nil;

	while (!nilp(bs)) {
		b = car(bs);
		if (car(b).value.symbol == symbol.value.symbol) {
			cdr(b) = value;
			return Error_OK;
		}
		bs = cdr(bs);
	}

	b = cons(symbol, value);
	cdr(env) = cons(b, cdr(env));

	return Error_OK;
}

int listp(Atom expr)
{
	while (!nilp(expr)) {
		if (expr.type != AtomType_Pair)
			return 0;
		expr = cdr(expr);
	}
	return 1;
}

Atom copy_list(Atom list)
{
	Atom a, p;

	if (nilp(list))
		return nil;

	a = cons(car(list), nil);
	p = a;
	list = cdr(list);

	while (!nilp(list)) {
		cdr(p) = cons(car(list), nil);
		p = cdr(p);
		list = cdr(list);
	}

	return a;
}

Error eval_expr(Atom expr, Atom env, Atom *result)
{
	Atom op, args, p;
	Error err;

	if (expr.type == AtomType_Symbol) {
		return env_get(env, expr, result);
	}
	else if (expr.type != AtomType_Pair) {
		*result = expr;
		return Error_OK;
	}

	if (!listp(expr))
		return Error_Syntax;

	op = car(expr);
	args = cdr(expr);

	if (op.type == AtomType_Symbol) {
/*		if (strcmp(op.value.symbol, "quote") == 0) { */
		if (op.value.symbol == sym_quote.value.symbol) {
			if (nilp(args) || !nilp(cdr(args)))
				return Error_Args;

			*result = car(args);
			return Error_OK;
		}
/*		else if (strcmp(op.value.symbol, "define") == 0) { */
		else if (op.value.symbol == sym_define.value.symbol) {
			Atom sym, val;

			if (nilp(args) || nilp(cdr(args)))
				return Error_Args;

			sym = car(args);
			if (sym.type == AtomType_Pair) {
				err = make_closure(env, cdr(sym), cdr(args), &val);
				sym = car(sym);
				if (sym.type != AtomType_Symbol)
					return Error_Type;
			}
			else if (sym.type == AtomType_Symbol) {
				if (!nilp(cdr(cdr(args))))
					return Error_Args;
				err = eval_expr(car(cdr(args)), env, &val);
			}
			else {
				return Error_Type;
			}

			if (err)
				return err;

			*result = sym;
			return env_set(env, sym, val);
		}
/*		else if (strcmp(op.value.symbol, "lambda") == 0) { */
		else if (op.value.symbol == sym_lambda.value.symbol) {
			if (nilp(args) || nilp(cdr(args)))
				return Error_Args;

			return make_closure(env, car(args), cdr(args), result);
		}
/*		else if (strcmp(op.value.symbol, "if") == 0) { */
		else if (op.value.symbol == sym_if.value.symbol) {
			Atom cond, val;

			if (nilp(args) || nilp(cdr(args)) || nilp(cdr(cdr(args)))
				|| !nilp(cdr(cdr(cdr(args)))))
				return Error_Args;

			err = eval_expr(car(args), env, &cond);
			if (err)
				return err;

			val = nilp(cond) ? car(cdr(cdr(args))) : car(cdr(args));
			return eval_expr(val, env, result);
		}
/*		else if (strcmp(op.value.symbol, "defmacro") == 0) { */
		else if (op.value.symbol == sym_defmacro.value.symbol) {
			Atom name, macro;
			Error err;

			if (nilp(args) || nilp(cdr(args)))
				return Error_Args;

			if (car(args).type != AtomType_Pair)
				return Error_Syntax;

			name = car(car(args));
			if (name.type != AtomType_Symbol)
				return Error_Type;

			err = make_closure(env, cdr(car(args)),
				cdr(args), &macro);
			if (err)
				return err;

			macro.type = AtomType_Macro;
			*result = name;
			return env_set(env, name, macro);
		}
/*		else if (strcmp(op.value.symbol, "and") == 0) { */
		else if (op.value.symbol == sym_and.value.symbol) {
			*result = sym_t;
			err = Error_OK;
			while (!nilp(args)) {
				err = eval_expr(car(args), env, result);
				if (nilp(*result))
					return err;
				args = cdr(args);
			}
			return err;			
		}
	}
	/* Evaluate operator */
	err = eval_expr(op, env, &op);
	if (err)
		return err;

	/* Is it a macro? */
	if (op.type == AtomType_Macro) {
		Atom expansion;
		op.type = AtomType_Closure;
		err = apply(op, args, &expansion);
		if (err)
			return err;
		return eval_expr(expansion, env, result);
	}

	/* Evaulate arguments */
	args = copy_list(args);
	p = args;
	while (!nilp(p)) {
		err = eval_expr(car(p), env, &car(p));
		if (err)
			return err;

		p = cdr(p);
	}

	return apply(op, args, result);
}

Error apply(Atom fn, Atom args, Atom *result)
{
	Atom env, arg_names, body;

	if (fn.type == AtomType_Builtin)
		return (*fn.value.builtin)(args, result);
	else if (fn.type != AtomType_Closure)
		return Error_Type;

	env = env_create(car(fn));
	arg_names = car(cdr(fn));
	body = cdr(cdr(fn));

	/* Bind the arguments */
	while (!nilp(arg_names)) {
		if (arg_names.type == AtomType_Symbol) {
			env_set(env, arg_names, args);
			args = nil;
			break;
		}

		if (nilp(args))
			return Error_Args;
		env_set(env, car(arg_names), car(args));
		arg_names = cdr(arg_names);
		args = cdr(args);
	}
	if (!nilp(args))
		return Error_Args;

	/* Evaluate the body */
	while (!nilp(body)) {
		Error err = eval_expr(car(body), env, result);
		if (err)
			return err;
		body = cdr(body);
	}

	return Error_OK;

}

Error builtin_car(Atom args, Atom *result)
{
	if (nilp(args) || !nilp(cdr(args)))
		return Error_Args;

	if (nilp(car(args)))
		*result = nil;
	else if (car(args).type != AtomType_Pair)
		return Error_Type;
	else
		*result = car(car(args));

	return Error_OK;
}

Error builtin_cdr(Atom args, Atom *result)
{
	if (nilp(args) || !nilp(cdr(args)))
		return Error_Args;

	if (nilp(car(args)))
		*result = nil;
	else if (car(args).type != AtomType_Pair)
		return Error_Type;
	else
		*result = cdr(car(args));

	return Error_OK;
}

Error builtin_cons(Atom args, Atom *result)
{
	if (nilp(args) || nilp(cdr(args)) || !nilp(cdr(cdr(args))))
		return Error_Args;

	*result = cons(car(args), car(cdr(args)));

	return Error_OK;
}

Error builtin_add(Atom args, Atom *result)
{
	Atom a, b;

	if (nilp(args) || nilp(cdr(args)) || !nilp(cdr(cdr(args))))
		return Error_Args;

	a = car(args);
	b = car(cdr(args));

	if (a.type != AtomType_Integer || b.type != AtomType_Integer)
		return Error_Type;

	*result = make_int(a.value.integer + b.value.integer);

	return Error_OK;
}

Error builtin_subtract(Atom args, Atom *result)
{
	Atom a, b;

	if (nilp(args) || nilp(cdr(args)) || !nilp(cdr(cdr(args))))
		return Error_Args;

	a = car(args);
	b = car(cdr(args));

	if (a.type != AtomType_Integer || b.type != AtomType_Integer)
		return Error_Type;

	*result = make_int(a.value.integer - b.value.integer);

	return Error_OK;
}

Error builtin_multiply(Atom args, Atom *result)
{
	Atom a, b;

	if (nilp(args) || nilp(cdr(args)) || !nilp(cdr(cdr(args))))
		return Error_Args;

	a = car(args);
	b = car(cdr(args));

	if (a.type != AtomType_Integer || b.type != AtomType_Integer)
		return Error_Type;

	*result = make_int(a.value.integer * b.value.integer);

	return Error_OK;
}

Error builtin_divide(Atom args, Atom *result)
{
	Atom a, b;

	if (nilp(args) || nilp(cdr(args)) || !nilp(cdr(cdr(args))))
		return Error_Args;

	a = car(args);
	b = car(cdr(args));

	if (a.type != AtomType_Integer || b.type != AtomType_Integer)
		return Error_Type;

	*result = make_int(a.value.integer / b.value.integer);

	return Error_OK;
}

Error builtin_numeq(Atom args, Atom *result)
{
	Atom a, b;

	if (nilp(args) || nilp(cdr(args)) || !nilp(cdr(cdr(args))))
		return Error_Args;

	a = car(args);
	b = car(cdr(args));

	if (a.type != AtomType_Integer || b.type != AtomType_Integer)
		return Error_Type;

	*result = (a.value.integer == b.value.integer) ? sym_t : nil;

	return Error_OK;
}

Error builtin_less(Atom args, Atom *result)
{
	Atom a, b;

	if (nilp(args) || nilp(cdr(args)) || !nilp(cdr(cdr(args))))
		return Error_Args;

	a = car(args);
	b = car(cdr(args));

	if (a.type != AtomType_Integer || b.type != AtomType_Integer)
		return Error_Type;

	*result = (a.value.integer < b.value.integer) ? sym_t : nil;

	return Error_OK;
}

Error builtin_apply(Atom args, Atom *result)
{
	Atom fn;

	if (nilp(args) || nilp(cdr(args)) || !nilp(cdr(cdr(args))))
		return Error_Args;

	fn = car(args);
	args = car(cdr(args));

	if (!listp(args))
		return Error_Syntax;

	return apply(fn, args, result);
}

Error builtin_eq(Atom args, Atom *result)
{
	Atom a, b;
	int eq = 0;

	if (nilp(args) || nilp(cdr(args)) || !nilp(cdr(cdr(args))))
		return Error_Args;

	a = car(args);
	b = car(cdr(args));

	if (a.type == b.type) {
		switch (a.type) {
		case AtomType_Nil:
			eq = 1;
			break;
		case AtomType_Pair:
		case AtomType_Closure:
		case AtomType_Macro:
			eq = (a.value.pair == b.value.pair);
			break;
		case AtomType_Symbol:
			eq = (a.value.symbol == b.value.symbol);
			break;
		case AtomType_Integer:
			eq = (a.value.integer == b.value.integer);
			break;
		case AtomType_Builtin:
			eq = (a.value.builtin == b.value.builtin);
			break;
		default:
			/* impossible */
			break;
		}
	}

	*result = eq ? sym_t : nil;
	return Error_OK;
}

Error builtin_pairp(Atom args, Atom *result)
{
	if (nilp(args) || !nilp(cdr(args)))
		return Error_Args;

	*result = (car(args).type == AtomType_Pair) ? sym_t : nil;
	return Error_OK;
}

char *slurp(const char *path)
{
	FILE *file;
	char *buf;
	long len;

	file = fopen(path, "rb");
	if (!file)
		return NULL;
	fseek(file, 0, SEEK_END);
	len = ftell(file);
	fseek(file, 0, SEEK_SET);

	buf = (char *)malloc(len + 1);
	if (!buf)
		return NULL;

	fread(buf, 1, len, file);
	buf[len] = 0;
	fclose(file);

	return buf;
}

void load_file(Atom env, const char *path)
{
	char *text;

	printf("Reading %s...\n", path);
	text = slurp(path);
	if (text) {
		const char *p = text;
		Atom expr;
		while (read_expr(p, &p, &expr) == Error_OK) {
			Atom result;
			Error err = eval_expr(expr, env, &result);
			if (err) {
				printf("Error in expression:\n\t");
				print_expr(expr);
				putchar('\n');
			}
			else {
				print_expr(result);
				putchar('\n');
			}
			gc_mark(env);
			gc();
		}
		free(text);
	}
}

int main(int argc, char **argv)
{
	Atom env;
	char *input;

	env = env_create(nil);

	/* Set up the initial environment */
	sym_t = make_sym("t");
	sym_quote = make_sym("quote");
	sym_define = make_sym("define");
	sym_lambda = make_sym("lambda");
	sym_if = make_sym("if");
	sym_defmacro = make_sym("defmacro");
	sym_and = make_sym("and");

	env_set(env, make_sym("car"), make_builtin(builtin_car));
	env_set(env, make_sym("cdr"), make_builtin(builtin_cdr));
	env_set(env, make_sym("cons"), make_builtin(builtin_cons));
	env_set(env, make_sym("+"), make_builtin(builtin_add));
	env_set(env, make_sym("-"), make_builtin(builtin_subtract));
	env_set(env, make_sym("*"), make_builtin(builtin_multiply));
	env_set(env, make_sym("/"), make_builtin(builtin_divide));
	env_set(env, sym_t, sym_t);
	env_set(env, make_sym("="), make_builtin(builtin_numeq));
	env_set(env, make_sym("<"), make_builtin(builtin_less));
	env_set(env, make_sym("apply"), make_builtin(builtin_apply));
	env_set(env, make_sym("eq?"), make_builtin(builtin_eq));
	env_set(env, make_sym("pair?"), make_builtin(builtin_pairp));	

	load_file(env, "library.lisp");

	while ((input = readline("> ")) != NULL) {
		char *buf = (char *)malloc(strlen(input) + 3);
		sprintf(buf, "(%s)", input);
		const char *p = buf;
		Error err;
		Atom expr, result;

		err = read_expr(p, &p, &expr);

		while (!nilp(expr)) {
			if (!err)
				err = eval_expr(car(expr), env, &result);

			switch (err) {
			case Error_OK:
				print_expr(result);
				putchar('\n');
				break;
			case Error_Syntax:
				puts("Syntax error");
				break;
			case Error_Unbound:
				puts("Symbol not bound");
				break;
			case Error_Args:
				puts("Wrong number of arguments");
				break;
			case Error_Type:
				puts("Wrong type");
				break;
			}
			expr = cdr(expr);
		}

		free(buf);
		free(input);
		gc_mark(env);
		gc();
	}

	return 0;
}

