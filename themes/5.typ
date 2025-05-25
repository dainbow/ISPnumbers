#import "../conf.typ": *

= Об оптимальных константах

#definition[
  Набор констант $C_r$ называется *оптимальным*, если:
  - Для любых $n >= 1, r >= 1, f in W^r (M), M > 0$ для констант $C_r$ выполнено неравенство
  #eq[
    $epsilon(f, cal(T)_(2 n - 1)) < C_r M / n^r quad f in W^r (M)$
  ]
  - Если $0 < c < C_r$ для некоторого $r >= 1$, то
  #eq[
    $forall n >= 1: forall M > 0: exists f in W^r (M): epsilon(f, cal(T)_(2 n - 1)) > c M / n^r$
  ]
]

#definition(title: "Функция Бернулли")[
  Пусть $r >= 1$. $r$-й функцией Бернулли называется функция
  #eq[
    $B_r (t) = sum_(k = 1)^oo cos(k t - pi r / 2) / k^r$
  ]
]

#lemma(title: "О тригонометрической интерполяции")[
  + Пусть $t_0, ..., t_(n - 1) in (0, pi)$ -- попарно различные точки и $b_0, ..., b_(n - 1) in RR$ -- произвольные числа. Тогда существует единственный чётный тригонометрический многочлен
  #eq[
    $T(t) = sum_(k = 0)^(n - 1) alpha_k cos(k t) quad alpha_k in RR$
  ]
  для которого $T(t_j) = b_j$ при $0 <= j <= n - 1$.
  + Пусть $tau_1, ..., tau_(n - 1) in (0, pi)$ -- попарно различные точки и $d_1, ..., d_(n - 1) in RR$ -- произвольные числа. Тогда существует единственный нечётный тригонометрический многочлен
  #eq[
    $T(t) = sum_(k = 1)^(n - 1) beta_k sin(k t) quad beta_k in RR$
  ]
  для которого $T(tau_j) = d_j$ при $1 <= j <= n - 1$.
]

#definition[
  Определим тригонометрические многочлены $T_(n, r) (t)$.

  Пусть $n >= 1$ и $t_j = ((2 j + 1) pi) / (2 n)$ -- все нули функции $cos(n t)$ на интервале $(0, pi)$, а $tau_k = (k pi) / n$ -- все нули функции $sin(n t)$ на интервале $(0, pi)$.

  Для чётного $r >= 2$ пусть $T_(n, r) (t) in cal(T)_(2 n - 1)$ -- тригонометрический многочлен, для которого $T_(n, r) (t_j) = B_r (t_j)$.

  Для нечётного $r >= 2$ пусть $T_(n, r) in cal(T)_(2 n - 1)$ -- тригонометрический многочлен, для которого $T_(n, r) (tau_k) = B_r (tau_k)$. Согласно лемме о тригонометрической интерполяции, функции $T_(n, r)$ определены однозначно.
]

#definition(title: "Класс гладких функций")[
  #eq[
    $W_*^r (M) = {f in C^r [S^1] | norm(f^((r))) <= M}$
  ]
]

#lemma(title: "Формула обращения")[
  Пусть $f in W^r_* (M)$. Тогда
  #eq[
    $f(t) = 1 / (2 pi) integral_0^(2 pi) f(tau) dif tau + 1 / pi integral_0^(2 pi) B_r (t - tau) f^((r)) (tau) dif tau$
  ]
] <reverse_formula>

#proof[
  Достаточно доказать для $r = 1$. имеем
  #eq[
    $1 / (2 pi) integral_0^(2 pi) f(tau) dif tau + 1 / pi integral_0^(2 pi) B_1 (t - tau) f' (tau) dif tau = \
    1 / (2 pi) integral_0^(2 pi) f(tau) dif tau + 1 / pi integral_0^t B_1 (t - tau) f' (tau) dif tau + 1 / pi integral_t^(2 pi) B_1 (t - tau + 2 pi) f' (tau) dif tau = \
    1 / (2pi) integral_0^(2pi) f(tau) dif tau + 1 / pi integral_0^t (pi - t + tau) / 2 f'(tau) dif tau + 1 / pi integral_t^(2pi) (tau - t - pi) / 2 f' (tau) dif tau = \
    1 / (2 pi) integral_0^(2 pi )f (tau) dif tau + 1 / pi integral_0^(2 pi) (tau -t )/2 f'(tau) dif tau + 1/2 integral_0^t f'(tau) dif tau - 1 / 2 integral_t^(2 pi) f'(tau) dif tau =\
    1 / (2 pi) integral_0^(2 pi) f(tau) dif tau + 1 / (2pi) integral_0^(2pi) tau f'(tau) dif tau + f(t) underset(=, "По частям") f(t)$
  ]
]

#lemma(title: "О нулях тригонометрической интерполяции")[
  Разность $Delta (t) = Delta_(n, r) (t) = B_r (t) - T_(n, r) (t)$ обращается в нуль на интервале $(0, pi)$ при $n >= 1$ и чётном $r$ только в точках $t_j$, а в нечётном $r$ только в точках $tau_k$.

  При $n = 1$ и нечётном $r$ корней на $(0, pi)$ нет. Все корни являются простыми.
] <interval_simple_roots>

#lemma[
  Пусть $n >= 1$ -- натуральное и $2 pi / n$-периодическая функция $f: RR -> RR$ суммируема на каждом конечном отрезке.

  Тогда для любого $1 <= k <= n - 1$:
  #eq[
    $integral_(-pi)^pi f(t) cos (k t) dif t = integral_(-pi)^pi f(t) sin (k t) dif t = 0$
  ]
] <integral_zero_sincos>

#lemma[
  Коэффициенты Фурье для функции Бернулли $B_r (t)$ выражаются формулой
  #eq[
    $mu_(r, n) + i nu_(r, n) = 1 / pi integral_(-pi)^pi B_r (t) d^(i n t) dif t = i^r / n^r quad n > 0$
  ]
  и
  #eq[
    $mu_(r, 0) + i nu_(r, 0) = 1 / pi integral_(-pi)^pi B_r (t) dif t = 0$
  ]
] <bernully_fourie>

#theorem(title: "Фавара")[
  Пусть
  #eq[
    $K_r = 4 / pi sum_(m = 0)^oo (-1)^(m (r + 1)) / (2 m + 1)^(r + 1) quad r >= 1$
  ]
  Тогда для любых $f in W^r (M)$ и $n >= 1$ справедливо неравенство
  #eq[
    $epsilon (f, cal(T)_(2 n - 1)) <= K_r M / n^r quad r >= 1 quad n >= 1$
  ]
]

#proof[
  Согласно @reverse_formula выполняется равенство
  #eq[
    $f(t) = a / 2 + 1 / pi integral_0^(2pi) B_r (t - tau) f^((r)) (tau) dif tau$
  ]
  Пусть $T in cal(T)_(2 n -1)$ произвольный тригонометрический многочлен степени $< n$. Тогда
  #eq[
    $Lambda(T) (t) = 1 / pi integral_(-pi)^pi T(t - tau) f^((r)) (tau) dif tau$
  ]
  также является тригонометрическим многочленом степени $< n$. Рассмотрим разность
  #eq[
    $f(t) - a / 2 - Lambda(T)(t) = 1 / pi integral_0^(2 pi) (B_r (t - tau) - T(t - tau))f^((r)) (tau) dif tau$
  ]
  Тогда
  #eq[
    $abs(f(t) - a / 2 - Lambda(T)(t)) <= 1 / pi integral_0^(2pi) abs(B_r (t - tau) - T(t -tau))abs(f^((r)) (tau)) dif tau <= \
    M / pi integral_0^(2pi) abs(B_r (z) - T(z)) dif z$
  ]
  Следовательно,
  #eq[
    $epsilon(f, cal(T)_(2 n - 1)) <= M / pi inf_(T in cal(T)_(2 n - 1)) integral_0^(2pi) abs(B_r (z) - T(z)) dif z$
  ]
  Значит достаточно проверить нерпвенство
  #eq[
    $inf_(T in cal(T)_(2 n - 1)) integral_0^(2pi) abs(B_r (z) - T(z)) dif z <= pi K_r n^(-r)$
  ]
  А для этого достаточно проверить, что, например,
  #eq[
    $integral_0^(2pi) abs(B_r (z) - T_(n, r) (z)) dif z <= pi K_r n^(-r)$
  ]
  Согласно @interval_simple_roots все корни разности $B_r (t) - T_(n , r) (t)$ на интервале $(0, pi)$ простые и совпадают с простыми корнями функции $cos(n t)$ при чётном $r$ и с корнями $sin(n t)$ при нечётном $r$.

  Поэтому знаки функций $B_r (t) - T_(n, r) (t)$ и $cos(n t)$ при чётном $r$ и, соответственно, $sin(n t)$ при нечётном $r$, либо всюду совпадают, либо всюду противоположны. Поэтому при БОО чётном $r$ выполняется равенство
  #eq[
    $integral_(-pi)^pi abs(B_r (z) - T_(n, r) (z)) dif z = 2 integral_0^pi abs(B_r (z) - T_(n , r) (z)) dif z = \
    2 integral_0^pi (B_r (z) - T_(n, r) (z)) sign Delta(z) dif z = plus.minus 2 integral_0^pi (B_r (z) - T_(n, r) (z)) sign cos(n z) dif z = \
    2 abs(integral_0^pi (B_r (z) - T_(n, r)) sign cos(n z) dif z) = abs(integral_(-pi)^pi (B_r (z) - T_(n, r) (z)) sign cos(n z) dif z) =\
    abs(integral_(-pi)^pi B_r (z) sign cos(n z) dif z)$
  ]
  где в последнем равенстве использована @integral_zero_sincos.

  Абсолютно такое же равенство (но с $sign sin(n z)$) аналогично получаем для нечётного $r$.

  Теперь воспользуемся обобщённым равенством Парсеваля в $L_2 [-pi, pi]$:
  #eq[
    $1 / pi integral_(-pi)^pi f(t) g(t) = (alpha_0 a_0) / 2 + sum_(k = 1)^oo (alpha_k a_k + beta_k b_k)$
  ]
  где $alpha_k, beta_k$ и $a_k, b_k$ -- коэффициенты Фурье функций $f(t)$ и $g(t)$ соответственно.

  Для функции Бернулли коэффициенты Фурье вычислены в @bernully_fourie. Для функции $sign cos(n t)$ и $sign sin(n t)$ соответствующие ряды Фурье определяются формулами
  #eq[
    $sign cos(n t) = 4 / pi sum_(k = 0)^oo (-1)^k (cos(2 k + 1) n t) / (2 k + 1)$
  ]
  и
  #eq[
    $sign sin(n t) = 4 / pi sum_(k = 0)^oo (sin (2 k + 1) n t) / (2 k + 1)$
  ]
  Подставляя полученные коэффициенты в равенства Парсеваля получим при чётном $r = 2 nu$:
  #eq[
    $1 / pi integral_(-pi)^pi B_(2 nu) (z) sign cos(n z) dif z = (-1)^nu 4 / (pi n^(2 nu)) sum_(k = 0)^oo (-1)^k / (2k + 1)^(2nu + 1) = ((-1)^nu K_r) / n^r$
  ]
  и нечётном $r = 2nu + 1$
  #eq[
    $1 / pi integral_(-pi)^pi B_(2nu + 1) (z) sign sin(n z) dif z = (-1)^nu 4 / (pi n^(2nu + 1)) sum_(k = 0)^oo 1 / (2k + 1)^(2nu + 2) = ((-1)^nu K_r) / n^r$
  ]
  Следовательно,
  #eq[
    $1 / pi integral_0^(2pi) abs(B_r (z) - T_(n, r) (z)) dif z = K_r n^(-r)$
  ]
  Что и требовалось доказать.
]

#pagebreak()
