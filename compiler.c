/* 
 *  编译原理实验报告
 *  简易的C语言编译器实现
 * **/

#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>

#define int long long    //实现64位地址工作模式
	
int token;              //当前输入
int token_val;          //当前输入的值
char *src, *old_src;	//指向源代码字符串的指针
int poolsize;
int line;				//行数
int *text;              //代码段
int *old_text;
int *stack;             //栈
char *data;             //数据段，只存放源代码的字符串

//PC 程序计数器，它存放的是一个内存地址，该地址中存放着下一条要执行的计算机指令。
//SP 指针寄存器，永远指向当前的栈顶。注意的是由于栈是位于高地址并向低地址增长的，所以入栈时SP的值减小。
//BP 基址指针。也是用于指向栈的某些位置，在调用函数时会使用到它。
//AX 通用寄存器，我们的虚拟机中，它用于存放一条指令执行后的结果。

int *pc, *bp, *sp, ax, cycle;   //虚拟机的寄存器
int *current_id;
int *symbols;		//符号表
int *idmain;		//main函数

//构建自己的虚拟机的指令，基于X86
enum{ LEA, IMM, JMP, CALL, JZ, JNZ, ENT, ADJ, LEV, LI, LC, SI, SC, PUSH, OR, XOR, AND, EQ, NE, LT, GT, LE, GE, SHL, SHR, ADD, SUB , MUL, DIV, MOD, OPEN, READ, CLOS, PRTF, MALC, MSET, MCMP, EXIT};


enum{
	Num = 128, Fun, Sys, Glo, Loc, Id,
	Char, Else, Enum, If, Int, Return, Sizeof, While,
	Assign, Cond, Lor, Lan, Or, Xor, And, Eq, Ne, Lt, Gt, Le, Ge, Shl, Shr, Add, Sub, Mul, Div, Mod, Inc, Dec, Brak};


enum{
	Token,//该标识符返回的标记
	Hash, //标识符的哈希值，用于标识符的快速比较
	Name, //存放标识符本身的字符串
	Type, //标识符的类型，即如果它是个变量，变量是 int 型、char 型还是指针型
	Class, //该标识符的类别，如数字，全局变量或局部变量等
	Value, //存放这个标识符的值，如标识符是函数，刚存放函数的地址
	
	//当局部标识符的名字与全局标识符相同时，用作保存全局标识符的信息
	BType, 
	BClass, 
	BValue, 
	IdSize
};

enum{
	CHAR, INT, PTR
};


int basetype;
int expr_type;
int index_of_bp;


//词法分析器主体, 每次调用该函数则返回下一个标记
void next() {
	char *last_pos;
	int hash;
	//跳过这些我们不识别的字符，我们同时还用它来处理空白字符
	while (token = *src) {

		++src;

		//遇到换行符，我们需要将当前的行号加一
		if (token == '\n') {
			++line;
		}
		else if (token == '#') {
			//跳过宏
			while (*src != 0 && *src != '\n') {
				src++;
			}
		}
		else if ((token >= 'a' && token <= 'z') || (token >= 'A' && token <= 'Z') || (token == '_')) {

			//分析标识符(变量名)
			last_pos = src - 1;
			hash = token;

			while ((*src >= 'a' && *src <= 'z') || (*src >= 'A' && *src <= 'Z') || (*src >= '0' && *src <= '9') || (*src == '_')) {
				hash = hash * 147 + *src;
				src++;
			}

			//将标识符的信息存入symbols内存区域中 
			current_id = symbols;
			while (current_id[Token]) {
				if (current_id[Hash] == hash && !memcmp((char *)current_id[Name], last_pos, src - last_pos)) {
					//symbols中已经存在该标识符
					token = current_id[Token];
					return;
				}
				current_id = current_id + IdSize;//IdSize=9, sizeof(current_id)=8
			}


			// 存储新的 ID
			current_id[Name] = (int)last_pos;
			current_id[Hash] = hash;
			token = current_id[Token] = Id;
			return;
		}
		else if (token >= '0' && token <= '9') {
			// dec(123) hex(0x123) oct(017)，分析数字，十进制，十六进制，八进制
			token_val = token - '0';
			if (token_val > 0) {
				// 十进制起始数字的范围：[1-9]
				while (*src >= '0' && *src <= '9') {
					token_val = token_val*10 + *src++ - '0';
				}
			} else {
				// 十六进制，从0开始
				if (*src == 'x' || *src == 'X') {
					//分析十六进制，字符a对应的十六进制值是 61, A是41，故通过 (token & 15) 可以得到个位数的值
					token = *++src;
					while ((token >= '0' && token <= '9') || (token >= 'a' && token <= 'f') || (token >= 'A' && token <= 'F')) {
						token_val = token_val * 16 + (token & 15) + (token >= 'A' ? 9 : 0);
						token = *++src;
					}
				} else {
					//八进制
					while (*src >= '0' && *src <= '7') {
						token_val = token_val*8 + *src++ - '0';
					}
				}
			}

			token = Num;
			return;
		}
		//分析字符串，分析到字符串，我们需要将它存放到 data 段中。然后返回它在 data 段中的地址；\n表示换行符，\a表示字符a的语法，如\"表示"。
		else if (token == '"' || token == '\'') {
			
			last_pos = data;
			while (*src != 0 && *src != token) {
				token_val = *src++;
				if (token_val == '\\') {
					token_val = *src++;
					if (token_val == 'n') {
						token_val = '\n';
					}
				}

				if (token == '"') {
					*data++ = token_val;
				}
			}

			src++;
			// 同时分析单个字符如 'a' 和字符串如 "a string"。若得到的是单个字符，我们以 Num 的形式返回
			if (token == '"') {
				token_val = (int)last_pos;
			} else {
				token = Num;
			}

			return;
		}
		else if (token == '/') {//只支持 // 类型的注释，不支持 /* comments */ 的注释
			if (*src == '/') {
				// 跳过注释
				while (*src != 0 && *src != '\n') {
					++src;
				}
			} else {
				// 除号
				token = Div;
				return;
			}
		}
		else if (token == '=') {
			//  '=='  '='
			if (*src == '=') {
				src ++;
				token = Eq;
			} else {
				token = Assign;
			}
			return;
		}
		else if (token == '+') {
			//  '+'  '++'
			if (*src == '+') {
				src ++;
				token = Inc;
			} else {
				token = Add;
			}
			return;
		}
		else if (token == '-') {
			//  '-'  '--'
			if (*src == '-') {
				src ++;
				token = Dec;
			} else {
				token = Sub;
			}
			return;
		}
		else if (token == '!') {
			// parse '!='
			if (*src == '=') {
				src++;
				token = Ne;
			}
			return;
		}
		else if (token == '<') {
			//  '<=', '<<' '<'
			if (*src == '=') {
				src ++;
				token = Le;
			} else if (*src == '<') {
				src ++;
				token = Shl;
			} else {
				token = Lt;
			}
			return;
		}
		else if (token == '>') {
			//  '>=', '>>' '>'
			if (*src == '=') {
				src ++;
				token = Ge;
			} else if (*src == '>') {
				src ++;
				token = Shr;
			} else {
				token = Gt;
			}
			return;
		}
		else if (token == '|') {
			//  '|'  '||'
			if (*src == '|') {
				src ++;
				token = Lor;
			} else {
				token = Or;
			}
			return;
		}
		else if (token == '&') {
			//  '&'  '&&'
			if (*src == '&') {
				src ++;
				token = Lan;
			} else {
				token = And;
			}
			return;
		}
		else if (token == '^') {
			token = Xor;
			return;
		}
		else if (token == '%') {
			token = Mod;
			return;
		}
		else if (token == '*') {
			token = Mul;
			return;
		}
		else if (token == '[') {
			token = Brak;
			return;
		}
		else if (token == '?') {
			token = Cond;
			return;
		}
		else if (token == '~' || token == ';' || token == '{' || token == '}' || token == '(' || token == ')' || token == ']' || token == ',' || token == ':') {
			// 
			return;
		}
	}
	return;
}

//将 next 函数包装起来，如果不是预期的标记则报错并退出。
void match(int tk) {
	if (token == tk) {
		next();
	} else {
		printf("%lld: expected token: %lld\n", line, tk);
		exit(-1);
	}
}

//分析表达式
void expression(int level) {
	// expressions have various format.
	// but majorly can be divided into two parts: unit and operator
	// for example `(char) *a[10] = (int *) func(b > 0 ? 10 : 20);
	// `a[10]` is an unit while `*` is an operator.
	// `func(...)` in total is an unit.
	// so we should first parse those unit and unary operators
	// and then the binary ones
	//
	// also the expression can be in the following types:
	//
	// 1. unit_unary ::= unit | unit unary_op | unary_op unit
	// 2. expr ::= unit_unary (bin_op unit_unary ...)

	// unit_unary()
	int *id;
	int tmp;
	int *addr;
	{
		if (!token) {
			printf("%lld: unexpected token EOF of expression\n", line);
			exit(-1);
		}
		if (token == Num) {
			match(Num);

			// emit code
			*++text = IMM;
			*++text = token_val;
			expr_type = INT;
		}
		else if (token == '"') {
			// continous string "abc" "abc"


			// emit code
			*++text = IMM;
			*++text = token_val;

			match('"');
			// store the rest strings
			while (token == '"') {
				match('"');
			}

			// append the end of string character '\0', all the data are default
			// to 0, so just move data one position forward.
			data = (char *)(((int)data + sizeof(int)) & (-sizeof(int)));
			expr_type = PTR;
		}
		else if (token == Sizeof) {
			// sizeof is actually an unary operator
			// 只支持 `sizeof(int)`, `sizeof(char)` and `sizeof(*...)` 
			match(Sizeof);
			match('(');
			expr_type = INT;

			if (token == Int) {
				match(Int);
			} else if (token == Char) {
				match(Char);
				expr_type = CHAR;
			}

			while (token == Mul) {
				match(Mul);
				expr_type = expr_type + PTR;
			}

			match(')');

			// emit code
			*++text = IMM;
			*++text = (expr_type == CHAR) ? sizeof(char) : sizeof(int);

			expr_type = INT;
		}
		else if (token == Id) {
			// there are several type when occurs to Id
			// but this is unit, so it can only be
			// 1. function call
			// 2. Enum variable
			// 3. global/local variable
			match(Id);

			id = current_id;

			if (token == '(') {
				// function call
				match('(');

				// pass in arguments
				tmp = 0; // number of arguments
				while (token != ')') {
					expression(Assign);
					*++text = PUSH;
					tmp ++;

					if (token == ',') {
						match(',');
					}

				}
				match(')');
				//判断函数的类型，如 printf, read, malloc 等等。内置函数有对应的汇编指令，而普通的函数则编译成 CALL <addr> 的形式。

				// emit code
				if (id[Class] == Sys) {
					// system functions
					*++text = id[Value];
				}
				else if (id[Class] == Fun) {
					// function call
					*++text = CALL;
					*++text = id[Value];
				}
				else {
					printf("%lld: bad function call\n", line);
					exit(-1);
				}

				// 清除入栈的参数。因为我们不在乎出栈的值，所以直接修改栈指针的大小即可。
				if (tmp > 0) {
					*++text = ADJ;
					*++text = tmp;
				}
				expr_type = id[Type];
			}
			else if (id[Class] == Num) {
				// 当该标识符是全局定义的枚举类型时，直接将对应的值用 IMM 指令存入 AX 即可
				*++text = IMM;
				*++text = id[Value];
				expr_type = INT;
			}
			else {
				// 用于加载变量的值，如果是局部变量则采用与 bp 指针相对位置的形式。而如果是全局变量则用 IMM 加载变量的地址。
				if (id[Class] == Loc) {
					*++text = LEA;
					*++text = index_of_bp - id[Value];
				}
				else if (id[Class] == Glo) {
					*++text = IMM;
					*++text = id[Value];
				}
				else {
					printf("%lld: undefined variable\n", line);
					exit(-1);
				}

				// 无论是全局还是局部变量，最终都根据它们的类型用 LC 或 LI 指令加载对应的值
				expr_type = id[Type];
				*++text = (expr_type == CHAR) ? LC : LI;
			}
		}
		else if (token == '(') {
			// cast or parenthesis
			match('(');
			if (token == Int || token == Char) {
				tmp = (token == Char) ? CHAR : INT; // cast type
				match(token);
				while (token == Mul) {
					match(Mul);
					tmp = tmp + PTR;
				}

				match(')');

				expression(Inc); // cast has precedence as Inc(++)

				expr_type  = tmp;
			} else {
				// normal parenthesis
				expression(Assign);
				match(')');
			}
		}
		else if (token == Mul) {
			// dereference *<addr>
			match(Mul);
			expression(Inc); // dereference has the same precedence as Inc(++)

			if (expr_type >= PTR) {
				expr_type = expr_type - PTR;
			} else {
				printf("%lld: bad dereference\n", line);
				exit(-1);
			}

			*++text = (expr_type == CHAR) ? LC : LI;
		}
		else if (token == And) {
			// get the address of
			match(And);
			expression(Inc); // get the address of
			if (*text == LC || *text == LI) {
				text --;
			} else {
				printf("%lld: bad address of\n", line);
				exit(-1);
			}

			expr_type = expr_type + PTR;
		}
		else if (token == '!') {
			// not
			match('!');
			expression(Inc);

			// emit code, use <expr> == 0
			*++text = PUSH;
			*++text = IMM;
			*++text = 0;
			*++text = EQ;

			expr_type = INT;
		}
		else if (token == '~') {
			// bitwise not
			match('~');
			expression(Inc);

			// emit code, use <expr> XOR -1
			*++text = PUSH;
			*++text = IMM;
			*++text = -1;
			*++text = XOR;

			expr_type = INT;
		}
		else if (token == Add) {
			// +var, do nothing
			match(Add);
			expression(Inc);

			expr_type = INT;
		}
		else if (token == Sub) {
			// -var
			match(Sub);

			if (token == Num) {
				*++text = IMM;
				*++text = -token_val;
				match(Num);
			} else {

				*++text = IMM;
				*++text = -1;
				*++text = PUSH;
				expression(Inc);
				*++text = MUL;
			}

			expr_type = INT;
		}
		else if (token == Inc || token == Dec) {
			tmp = token;
			match(token);
			expression(Inc);
			if (*text == LC) {
				*text = PUSH;  // to duplicate the address
				*++text = LC;
			} else if (*text == LI) {
				*text = PUSH;
				*++text = LI;
			} else {
				printf("%lld: bad lvalue of pre-increment\n", line);
				exit(-1);
			}
			*++text = PUSH;
			*++text = IMM;
			*++text = (expr_type > PTR) ? sizeof(int) : sizeof(char);
			*++text = (tmp == Inc) ? ADD : SUB;
			*++text = (expr_type == CHAR) ? SC : SI;
		}
		else {
			printf("%lld: bad expression\n", line);
			exit(-1);
		}
	}

	// binary operator and postfix operators.
	{
		while (token >= level) {
			// handle according to current operator's precedence
			tmp = expr_type;
			if (token == Assign) {
				// var = expr;
				match(Assign);
				if (*text == LC || *text == LI) {
					*text = PUSH; // save the lvalue's pointer
				} else {
					printf("%lld: bad lvalue in assignment\n", line);
					exit(-1);
				}
				expression(Assign);

				expr_type = tmp;
				*++text = (expr_type == CHAR) ? SC : SI;
			}
			else if (token == Cond) {
				// expr ? a : b;
				match(Cond);
				*++text = JZ;
				addr = ++text;
				expression(Assign);
				if (token == ':') {
					match(':');
				} else {
					printf("%lld: missing colon in conditional\n", line);
					exit(-1);
				}
				*addr = (int)(text + 3);
				*++text = JMP;
				addr = ++text;
				expression(Cond);
				*addr = (int)(text + 1);
			}
			else if (token == Lor) {
				// logic or
				match(Lor);
				*++text = JNZ;
				addr = ++text;
				expression(Lan);
				*addr = (int)(text + 1);
				expr_type = INT;
			}
			else if (token == Lan) {
				// logic and
				match(Lan);
				*++text = JZ;
				addr = ++text;
				expression(Or);
				*addr = (int)(text + 1);
				expr_type = INT;
			}
			else if (token == Or) {
				// bitwise or
				match(Or);
				*++text = PUSH;
				expression(Xor);
				*++text = OR;
				expr_type = INT;
			}
			else if (token == Xor) {
				// bitwise xor
				match(Xor);
				*++text = PUSH;
				expression(And);
				*++text = XOR;
				expr_type = INT;
			}
			else if (token == And) {
				// bitwise and
				match(And);
				*++text = PUSH;
				expression(Eq);
				*++text = AND;
				expr_type = INT;
			}
			else if (token == Eq) {
				// equal ==
				match(Eq);
				*++text = PUSH;
				expression(Ne);
				*++text = EQ;
				expr_type = INT;
			}
			else if (token == Ne) {
				// not equal !=
				match(Ne);
				*++text = PUSH;
				expression(Lt);
				*++text = NE;
				expr_type = INT;
			}
			else if (token == Lt) {
				// less than
				match(Lt);
				*++text = PUSH;
				expression(Shl);
				*++text = LT;
				expr_type = INT;
			}
			else if (token == Gt) {
				// greater than
				match(Gt);
				*++text = PUSH;
				expression(Shl);
				*++text = GT;
				expr_type = INT;
			}
			else if (token == Le) {
				// less than or equal to
				match(Le);
				*++text = PUSH;
				expression(Shl);
				*++text = LE;
				expr_type = INT;
			}
			else if (token == Ge) {
				// greater than or equal to
				match(Ge);
				*++text = PUSH;
				expression(Shl);
				*++text = GE;
				expr_type = INT;
			}
			else if (token == Shl) {
				// shift left
				match(Shl);
				*++text = PUSH;
				expression(Add);
				*++text = SHL;
				expr_type = INT;
			}
			else if (token == Shr) {
				// shift right
				match(Shr);
				*++text = PUSH;
				expression(Add);
				*++text = SHR;
				expr_type = INT;
			}
			else if (token == Add) {
				// add
				match(Add);
				*++text = PUSH;
				expression(Mul);

				expr_type = tmp;
				if (expr_type > PTR) {
					// pointer type, and not `char *`
					*++text = PUSH;
					*++text = IMM;
					*++text = sizeof(int);
					*++text = MUL;
				}
				*++text = ADD;
			}
			else if (token == Sub) {
				// sub
				match(Sub);
				*++text = PUSH;
				expression(Mul);
				if (tmp > PTR && tmp == expr_type) {
					// pointer subtraction
					*++text = SUB;
					*++text = PUSH;
					*++text = IMM;
					*++text = sizeof(int);
					*++text = DIV;
					expr_type = INT;
				} else if (tmp > PTR) {
					// pointer movement
					*++text = PUSH;
					*++text = IMM;
					*++text = sizeof(int);
					*++text = MUL;
					*++text = SUB;
					expr_type = tmp;
				} else {
					// numeral subtraction
					*++text = SUB;
					expr_type = tmp;
				}
			}
			else if (token == Mul) {
				// multiply
				match(Mul);
				*++text = PUSH;
				expression(Inc);
				*++text = MUL;
				expr_type = tmp;
			}
			else if (token == Div) {
				// divide
				match(Div);
				*++text = PUSH;
				expression(Inc);
				*++text = DIV;
				expr_type = tmp;
			}
			else if (token == Mod) {
				// Modulo
				match(Mod);
				*++text = PUSH;
				expression(Inc);
				*++text = MOD;
				expr_type = tmp;
			}
			else if (token == Inc || token == Dec) {
				// postfix inc(++) and dec(--)
				// we will increase the value to the variable and decrease it
				// on `ax` to get its original value.
				if (*text == LI) {
					*text = PUSH;
					*++text = LI;
				}
				else if (*text == LC) {
					*text = PUSH;
					*++text = LC;
				}
				else {
					printf("%lld: bad value in increment\n", line);
					exit(-1);
				}

				*++text = PUSH;
				*++text = IMM;
				*++text = (expr_type > PTR) ? sizeof(int) : sizeof(char);
				*++text = (token == Inc) ? ADD : SUB;
				*++text = (expr_type == CHAR) ? SC : SI;
				*++text = PUSH;
				*++text = IMM;
				*++text = (expr_type > PTR) ? sizeof(int) : sizeof(char);
				*++text = (token == Inc) ? SUB : ADD;
				match(token);
			}
			else if (token == Brak) {
				// array access var[xx]
				match(Brak);
				*++text = PUSH;
				expression(Assign);
				match(']');

				if (tmp > PTR) {
					// pointer, `not char *`
					*++text = PUSH;
					*++text = IMM;
					*++text = sizeof(int);
					*++text = MUL;
				}
				else if (tmp < PTR) {
					printf("%lld: pointer type expected\n", line);
					exit(-1);
				}
				expr_type = tmp - PTR;
				*++text = ADD;
				*++text = (expr_type == CHAR) ? LC : LI;
			}
			else {
				printf("%lld: compiler error, token = %lld\n", line, token);
				exit(-1);
			}
		}
	}
}
 
//分析语句
void statement() {
	// there are 6 kinds of statements here:
	// 1. if (...) <statement> [else <statement>]
	// 2. while (...) <statement>
	// 3. { <statement> }
	// 4. return xxx;
	// 5. <empty statement>;
	// 6. expression; (expression end with semicolon)

	int *a, *b; // bess for branch control

	if (token == If) {
		// if (...) <statement> [else <statement>]
		//
		//   if (...)           <cond>
		//                      JZ a
		//     <statement>      <statement>
		//   else:              JMP b
		// a:                 a:
		//     <statement>      <statement>
		// b:                 b:
		//
		match(If);
		match('(');
		expression(Assign);  // parse condition
		match(')');

		// emit code for if
		*++text = JZ;
		b = ++text;

		statement();         // parse statement
		if (token == Else) { // parse else
			match(Else);

			// emit code for JMP B
			*b = (int)(text + 3);
			*++text = JMP;
			b = ++text;

			statement();
		}

		*b = (int)(text + 1);
	}
	else if (token == While) {
		//
		// a:                     a:
		//    while (<cond>)        <cond>
		//                          JZ b
		//     <statement>          <statement>
		//                          JMP a
		// b:                     b:
		match(While);

		a = text + 1;

		match('(');
		expression(Assign);
		match(')');

		*++text = JZ;
		b = ++text;

		statement();

		*++text = JMP;
		*++text = (int)a;
		*b = (int)(text + 1);
	}
	else if (token == '{') {
		// { <statement> ... }
		match('{');

		while (token != '}') {
			statement();
		}

		match('}');
	}
	else if (token == Return) {
		// return [expression];
		match(Return);

		if (token != ';') {
			expression(Assign);
		}

		match(';');

		// emit code for return
		*++text = LEV;
	}
	else if (token == ';') {
		// empty statement
		match(';');
	}
	else {
		// a = b; or function_call();
		expression(Assign);
		match(';');
	}
}

void function_parameter() {
	int type;
	int params;
	params = 0;
	while (token != ')') {
		//与全局变量定义的解析一样，用于解析该参数的类型
		// int name, ...
		type = INT;
		if (token == Int) {
			match(Int);
		} else if (token == Char) {
			type = CHAR;
			match(Char);
		}

		// pointer type
		while (token == Mul) {
			match(Mul);
			type = type + PTR;
		}

		// parameter name
		if (token != Id) {
			printf("%lld: bad parameter declaration\n", line);
			exit(-1);
		}
		if (current_id[Class] == Loc) {
			printf("%lld: duplicate parameter declaration\n", line);
			exit(-1);
		}

		match(Id);
		// 存储局部变量，全局变量的信息保存（无论是是否真的在全局中用到了这个变量）在 BXXX 中，再赋上局部变量相关的信息
		current_id[BClass] = current_id[Class]; 
		current_id[Class]  = Loc;
		current_id[BType]  = current_id[Type];  
		current_id[Type]   = type;
		current_id[BValue] = current_id[Value]; 
		current_id[Value]  = params++;   // 当前参数的索引

		if (token == ',') {
			match(',');
		}
	}
	index_of_bp = params+1;
}

void function_body() {
	// type func_name (...) {...}
	//                   -->|   |<--

	// ... {
	// 1. local declarations
	// 2. statements
	// }

	int pos_local; // 局部变量在栈上的位置
	int type;
	pos_local = index_of_bp;

	while (token == Int || token == Char) {
		// 局部变量声明部分分析，与全局变量类似
		basetype = (token == Int) ? INT : CHAR;
		match(token);

		while (token != ';') {
			type = basetype;
			while (token == Mul) {
				match(Mul);
				type = type + PTR;
			}

			if (token != Id) {
				// invalid declaration
				printf("%lld: bad local declaration\n", line);
				exit(-1);
			}
			if (current_id[Class] == Loc) {
				// identifier exists
				printf("%lld: duplicate local declaration\n", line);
				exit(-1);
			}
			match(Id);

			// 存储局部变量
			current_id[BClass] = current_id[Class]; 
			current_id[Class]  = Loc;
			current_id[BType]  = current_id[Type];  
			current_id[Type]   = type;
			current_id[BValue] = current_id[Value];
			current_id[Value]  = ++pos_local;   // index of current parameter

			if (token == ',') {
				match(',');
			}
		}
		match(';');
	}

	// 在栈上为局部变量预留空间
	*++text = ENT;
	*++text = pos_local - index_of_bp;

	// statements
	while (token != '}') {
		statement();
	}

	// emit code for leaving the sub function
	*++text = LEV;
}

void function_declaration() {
	// type func_name (...) {...}
	//               | this part

	match('(');
	function_parameter();
	match(')');
	match('{');
	function_body();
	//match('}');
	//variable_decl与function_decl是放在一起解析的，而variable_decl是以字符;结束的。而function_decl是以字符}结束的，若在此通过match消耗了‘;’字符，那么外层的while循环就没法准确地知道函数定义已经结束。所以我们将结束符的解析放在了外层的while循环中


	// 将符号表中的信息恢复成全局的信息，局部变量是可以和全局变量同名的，一旦同名，在函数体内局部变量就会覆盖全局变量，出了函数体，全局变量就恢复了原先的作用。这段代码线性地遍历所有标识符，并将保存在BXXX中的信息还原。
	current_id = symbols;
	while (current_id[Token]) {
		if (current_id[Class] == Loc) {
			current_id[Class] = current_id[BClass];
			current_id[Type]  = current_id[BType];
			current_id[Value] = current_id[BValue];
		}
		current_id = current_id + IdSize;
	}
}

void enum_declaration() {
	// 解析枚举类型的定义 [id] { a = 1, b = 3, ...}
	int i;
	i = 0;
	while (token != '}') {
		if (token != Id) {
			printf("%lld: bad enum identifier %lld\n", line, token);
			exit(-1);
		}
		next();
		if (token == Assign) {
			// like {a=10}
			next();
			if (token != Num) {
				printf("%lld: bad enum initializer\n", line);
				exit(-1);
			}
			i = token_val;
			next();
		}

		current_id[Class] = Num;
		current_id[Type] = INT;
		current_id[Value] = i++;

		if (token == ',') {
			next();
		}
	}
}

//解析全局变量，全局的定义语句，包括变量定义，类型定义（只支持枚举）及函数定义
void global_declaration() {
	// global_declaration ::= enum_decl | variable_decl | function_decl
	//
	// enum_decl ::= 'enum' [id] '{' id ['=' 'num'] {',' id ['=' 'num'} '}'
	//
	// variable_decl ::= type {'*'} id { ',' {'*'} id } ';'
	//
	// function_decl ::= type {'*'} id '(' parameter_decl ')' '{' body_decl '}'


	int type; // tmp, actual type for variable
	int i; // tmp

	basetype = INT;

	// 分析枚举类型
	if (token == Enum) {
		// enum [id] { a = 10, b = 20, ... }
		match(Enum);
		if (token != '{') {
			match(Id); // skip the [id] part
		}
		if (token == '{') {
			// parse the assign part
			match('{');
			enum_declaration();
			match('}');
		}

		match(';');
		return;
	}

	// 解析类型信息
	if (token == Int) {
		match(Int);
	}
	else if (token == Char) {
		match(Char);
		basetype = CHAR;
	}
	
	//如果只解析到类型，如 int identifier 时我们并不能确定 identifier 是一个普通的变量还是一个函数，所以还需要继续查看后续的标记，如果遇到 ( 则可以断定是函数了，反之则是变量。
	// 解析逗号分隔的变量声明
	while (token != ';' && token != '}') {
		type = basetype;
		// 解析指针类型，注意可能存在 `int ****x;`
		while (token == Mul) {
			match(Mul);
			type = type + PTR;
		}

		if (token != Id) {
			// 无用的标识符
			printf("%lld: bad global declaration\n", line);
			exit(-1);
		}
		if (current_id[Class]) {
			// 标识符已存在
			printf("%lld: duplicate global declaration\n", line);
			exit(-1);
		}
		match(Id);
		current_id[Type] = type;

		if (token == '(') {
			current_id[Class] = Fun;
			current_id[Value] = (int)(text + 1); // 函数的地址
			function_declaration();
		} else {
			// 变量申明
			current_id[Class] = Glo; // 全局变量
			current_id[Value] = (int)data; // 全局变量存放在数据区
			data = data + sizeof(int);
		}

		if (token == ',') {
			match(',');
		}
	}
	next();
}

void program() {
	// get next token
	next();
	while (token > 0) {
		global_declaration();
	}
}

//虚拟机的入口，用来解释目标代码
int eval() {
	int op, *tmp;
	while (1) {
		op = *pc++;

		if (op == IMM)       {ax = *pc++;}                                     // load immediate value to ax
		else if (op == LC)   {ax = *(char *)ax;}                               // load character to ax, address in ax
		else if (op == LI)   {ax = *(int *)ax;}                                // load integer to ax, address in ax
		else if (op == SC)   {ax = *(char *)*sp++ = ax;}                       // save character to address, value in ax, address on stack
		else if (op == SI)   {*(int *)*sp++ = ax;}                             // save integer to address, value in ax, address on stack
		else if (op == PUSH) {*--sp = ax;}                                     // push the value of ax onto the stack
		else if (op == JMP)  {pc = (int *)*pc;}                                // jump to the address
		else if (op == JZ)   {pc = ax ? pc + 1 : (int *)*pc;}                   // jump if ax is zero
		else if (op == JNZ)  {pc = ax ? (int *)*pc : pc + 1;}                   // jump if ax is not zero
		else if (op == CALL) {*--sp = (int)(pc+1); pc = (int *)*pc;}           // call subroutine
		//else if (op == RET)  {pc = (int *)*sp++;}                              // return from subroutine;
		else if (op == ENT)  {*--sp = (int)bp; bp = sp; sp = sp - *pc++;}      // make new stack frame
		else if (op == ADJ)  {sp = sp + *pc++;}                                // add esp, <size>
		else if (op == LEV)  {sp = bp; bp = (int *)*sp++; pc = (int *)*sp++;}  // restore call frame and PC
		else if (op == ENT)  {*--sp = (int)bp; bp = sp; sp = sp - *pc++;}      // make new stack frame
		else if (op == ADJ)  {sp = sp + *pc++;}                                // add esp, <size>
		else if (op == LEV)  {sp = bp; bp = (int *)*sp++; pc = (int *)*sp++;}  // restore call frame and PC
		else if (op == LEA)  {ax = (int)(bp + *pc++);}                         // load address for arguments.

		else if (op == OR)  ax = *sp++ | ax;
		else if (op == XOR) ax = *sp++ ^ ax;
		else if (op == AND) ax = *sp++ & ax;
		else if (op == EQ)  ax = *sp++ == ax;
		else if (op == NE)  ax = *sp++ != ax;
		else if (op == LT)  ax = *sp++ < ax;
		else if (op == LE)  ax = *sp++ <= ax;
		else if (op == GT)  ax = *sp++ >  ax;
		else if (op == GE)  ax = *sp++ >= ax;
		else if (op == SHL) ax = *sp++ << ax;
		else if (op == SHR) ax = *sp++ >> ax;
		else if (op == ADD) ax = *sp++ + ax;
		else if (op == SUB) ax = *sp++ - ax;
		else if (op == MUL) ax = *sp++ * ax;
		else if (op == DIV) ax = *sp++ / ax;
		else if (op == MOD) ax = *sp++ % ax;


		else if (op == EXIT) { printf("exit(%lld)", *sp); return *sp;}
		else if (op == OPEN) { ax = open((char *)sp[1], sp[0]); }
		else if (op == CLOS) { ax = close(*sp);}
		else if (op == READ) { ax = read(sp[2], (char *)sp[1], *sp); }
		else if (op == PRTF) { tmp = sp + pc[1]; ax = printf((char *)tmp[-1], tmp[-2], tmp[-3], tmp[-4], tmp[-5], tmp[-6]); }
		else if (op == MALC) { ax = (int)malloc(*sp);}
		else if (op == MSET) { ax = (int)memset((char *)sp[2], sp[1], *sp);}
		else if (op == MCMP) { ax = memcmp((char *)sp[2], (char *)sp[1], *sp);}
		else {
			printf("unknown instruction:%lld\n", op);
			return -1;
		}
	}
	return 0;
}

#undef int // Mac/clang needs this to compile
int main(int argc, char **argv)
{
	#define int long long // to work with 64bit address

	int i, fd;
	int *tmp;

	argc--;
	argv++;

	

	poolsize = 256 * 1024; // 任意大小
	line = 1;

	if ((fd = open(*argv, 0)) < 0) {
		printf("could not open(%s)\n", *argv);
		return -1;
	}

	// 为虚拟机分配内存
	if (!(text = old_text = malloc(poolsize))) { //代码段
		printf("could not malloc(%lld) for text area\n", poolsize);
		return -1;
	}
	if (!(data = malloc(poolsize))) { //数据段
		printf("could not malloc(%lld) for data area\n", poolsize);
		return -1;
	}
	if (!(stack = malloc(poolsize))) { //栈区
		printf("could not malloc(%lld) for stack area\n", poolsize);
		return -1;
	}
	if (!(symbols = malloc(poolsize))) {
		printf("could not malloc(%lld) for symbol table\n", poolsize);
		return -1;
	}

	memset(text, 0, poolsize); //初始化内存
	memset(data, 0, poolsize);
	memset(stack, 0, poolsize);
	memset(symbols, 0, poolsize);
	bp = sp = (int *)((int)stack + poolsize);//栈由高地址向低地址扩展
	ax = 0; //ax寄存器
	//将它们加入符号表，并提前为它们赋予必要的信息
	src = "char else enum if int return sizeof while "
		  "open read close printf malloc memset memcmp exit void main";


	 // 向符号表中添加关键字
	i = Char; //Char=134
	while (i <= While) {
		next();
		current_id[Token] = i++;
	}

	// add library to symbol table
	i = OPEN;
	while (i <= EXIT) {
		next();
		current_id[Class] = Sys;
		current_id[Type] = INT;
		current_id[Value] = i++;
	}

	next(); 
	current_id[Token] = Char; // handle void type

	next(); 
	idmain = current_id; // keep track of main


	//代开源文件
	if ((fd = open(*argv, 0)) < 0) {
		printf("could not open(%s)\n", *argv);
		return -1;
	}

	if (!(src = old_src = malloc(poolsize))) {
		printf("could not malloc(%lld) for source area\n", poolsize);
		return -1;
	}
	// 读取源代码
	if ((i = read(fd, src, poolsize-1)) <= 0) {
		printf("read() returned %lld\n", i);
		return -1;
	}
	src[i] = 0; // 添加结束标记
	close(fd);

	program();

	if (!(pc = (int *)idmain[Value])) {
		printf("main() not defined\n");
		return -1;
	}

	// setup stack
	sp = (int *)((int)stack + poolsize);
	*--sp = EXIT; // call exit if main returns
	*--sp = PUSH; tmp = sp;
	*--sp = argc;
	*--sp = (int)argv;
	*--sp = (int)tmp;

	return eval();
}
