#import "../conf.typ": *

= О ядрах

#definition(title: "Ядро")[
  *Положительным ядро* называется последовательность $2 pi$-периодических функций $K_n (x)$, удовлетворяющая следующим свойствам:
  + $K_n (x) >= 0$
  + $integral_(-pi)^pi K_n (x) dif x = 1$
  + $lim_(n -> oo) integral_(-delta)^delta K_n (x) dif x = 1$ для всех $0 < delta < pi$
  Если выполняются лишь свойства 2 и 3, последовательность $K_n$ называется *ядром*.
]

#lemma(title: "Об аппроксимации положительного ядра")[
  Пусть $K_n (x)$ -- положительное ядро.

  Тогда для любой $2pi$-периодической функции $f(x)$ последовательность функций $f_n (x) = integral_(-pi)^pi f(t + x) K_n (t) dif t$ равномерно сходится к функции $f(x)$.
]

#proof[
  Ввиду свойств ядра имеем:
  #eq[
    $f(x) - integral_(-pi)^pi f(x + t) K_n (t) dif t = integral_(-pi)^pi f(x) K_n (t) dif t - integral_(-pi)^pi f(x + t) K_n (t) dif t = \
    integral_(-pi)^pi (f(x) - f(x + t))K_n (t) dif t = \
    (integral_(-pi)^(-delta) + integral_(-delta)^delta + integral_delta^pi) (f(x) - f(x + t))K_n (t) dif t$
  ]
  В силу непрерывности и периодичности функции $f(x)$, эта функция равномерно непрерывна и ограничена на всей числовой прямой. Поэтому
  #eq[
    $forall epsilon > 0 : exists delta > 0: forall x_1, x_2, abs(x_1 - x_2) < delta : abs(f(x_1) - f(x_2)) < epsilon / 2$
  ]
  и
  #eq[
    $exists M > 0: forall x: abs(f(x)) < M$
  ]
  Фиксируем такое $delta < pi$. Тогда ввиду неорицательности $K_n (t)$ имеем
  #eq[
    $abs(integral_(-delta)^delta (f(x) - f(x + t))) K_n (t) dif t <= integral_(-delta)^delta abs(f(x) - f(x + t)) K_n (t) dif t < \
    integral_(-delta)^delta epsilon / 2 K_n (t) dif t = epsilon / 2 integral_(-delta)^delta K_n (t) dif t$
  ]
  А в силу ограниченности функции $abs(f(x)) < M$ выполнено неравенство
  #eq[
    $(integral_(-pi)^(-delta) + integral_delta^pi) abs(f(x) - f(x + t))K_n (t) dif t <= 2 M (integral_(-pi)^(-delta) + integral_delta^pi) K_n (t) dif t = \
    2 M (1 - integral_(-delta)^delta K_n (t) dif t)$
  ]
  Получается,
  #eq[
    $abs(f(x) - integral_(-pi)^pi f(x + t) K_n (t) dif t) <= epsilon / 2 integral_(-delta)^delta K_n (t) dif t + 2 M (1 - integral_(-delta)^delta K_n (t) dif t) ->_(n -> oo) 0$
  ]
]

#lemma[
  Последовательность функций
  #eq[
    $D_n (x) = 1 / (2 pi) + 1 / pi sum_(k = 1)^(n - 1) cos k x = (sin(n - 1 / 2)x) / (2 pi sin (x / 2))$
  ]
  определяет ядро. Это ядро называется *ядром Дирихле*.
]

#proof[
  По определению функции $D_n$:
  #eq[
    $integral_(-pi)^pi D_n (t) dif t = integral_(-pi)^pi (dif x) / (2 pi) + 1 / pi sum_(k = 1)^(n - 1) integral_(-pi)^pi cos k t dif t = 1$
  ]
  Далее, пусть $0 < delta < pi$. Имеем
  #eq[
    $integral_(-pi)^pi D_n (t) dif t = 1 - (integral_(-pi)^(-delta) + integral_delta^pi) D_n (t) dif t$
  ]
  То есть, достаточно проверять, что $(integral_(-pi)^(-delta) + integral_delta^pi) D_n (t) dif t$ бесконечно малая величина.

  Рассмотрим функцию
  #eq[
    $g(x) = cases(0\, abs(x) < delta, 1\, delta <= abs(x) <= delta)$
  ]
  Положим $h(x) = g(x) / sin(x / 2) in L_2^* [-pi, pi]$. Тогда
  #eq[
    $(integral_(-pi)^(-delta) + integral_delta^pi) D_n (t) dif t = integral_(-pi)^pi h(t) sin (n - 1 / 2) t dif t = \
    integral_(-pi)^pi h(t) cos(t / 2) sin(n t) dif t - integral_(-pi)^pi h(t) sin(t / 2) cos(n t) dif t$
  ]
  Согласно неравенству Бесселя, последние два интеграла стремятся к нулю.
]

#lemma[
  Последовательность функций
  #eq[
    $Phi_n (x) = (sum_(k = 1)^n D_k (x)) / n$
  ]
  Определяет положительное ядро. Это ядро называется *ядром Фейера*.
]

#proof[
  По определению функции $Phi_n (x)$:
  #eq[
    $integral_(-pi)^pi Phi_n (t) dif t = 1 / n integral_(-pi)^pi sum_(k = 1)^n D_k (t) dif t = 1 / n sum_(k = 1)^n 1 = 1$
  ]
  Неравенство $Phi_n (t) >= 0$ следует из соотношения
  #eq[
    $Phi_n (t) = 1 / (4 pi n) (1 - cos(n t)) / (sin^2 (t / 2))$
  ]
  Фиксируем $0 < delta <= pi$. Функция
  #eq[
    $(1 - cos n t) / (sin^2 (t / (2 pi)))$
  ]
  ограничена на $[-pi, -delta] union [delta, pi]$. Следовательно, на этом множестве $Phi_n (t) arrow.twohead 0$. Поэтому требуемая бесконечная малость выполняется.
]

#lemma[
  Последовательность функций
  #eq[
    $J_n (x) = (3n^3) / (2 pi (2n^2 + 1)) (sin(n x / 2) / (n sin(x / 2)))^4 = (6 pi n) / (2 n^2 + 1) Phi^2_n (x)$
  ]
  определяет положительное ядро. Это ядро называется *ядром Джекснова*.
]

#definition[
  Пусть $M > 0$ и $r$ натуральное. Классом $W^r (M)$ называется множество $r - 1$ дифференцируемых $2 pi$-периодических функций, для который $f^((r - 1)) (x)$ -- M-липшецева.
]

#theorem(title: "Джексона")[
  Сущестувует такая константа $C$, что для любых $r, n, M > 0$ и $f in W^r (M)$ выполняется неравенство
  #eq[
    $epsilon(f, cal(T)_(2 n - 1)) < C^r M / n^r$
  ]
]

#proof[
  Заметим, что $J_n (x)$ тригонометрический многочлен степени $2(n - 1)$. Следовательно, $forall f in C[S^1]$
  #eq[
    $T_n (x) = integral_(-pi)^pi J_n (t - x) f(t) dif t$
  ]
  тригонометрический многочлен степени $<= 2(n - 1)$.

  Пусть $r = 1$ и $f in W^1 (M)$, для $m >= 1$ рассмотрим тригонометрический многочлен $T(x)$. Учитывая чётность ядра Джексона и условие Липшица для функции $f$, получаем
  #eq[
    $abs(f(x) - T(x)) = abs(integral_(-pi)^pi J_m (t) (f(x) - f(x + t)) dif t) <= M integral_(-pi)^pi abs(t) J_m (t) dif t = \
    2 M integral_0^pi t J_m (t) dif t$
  ]
  Ввиду неравенства $sin (t / 2) >= t / pi$ при $0 <= t <= pi$ получаем
  #eq[
    $integral_0^pi t J_m (t) dif t <= (3 pi^3) / (2 m (2 m^2 + 1)) integral_0^pi (sin^4 (m t / 2)) / t^3 dif t = \
    (3 pi^3 m) / (8 (2 m^2 + 1)) integral_0^(m pi / 2) (sin^4 (t)) / t^3 dif t < C / (4 m)$
  ]
  Следовательно, $norm(f - t) < (C M) / (2 m)$.

  Заметим, что $J_n (x) in cal(T)_(4 n - 1)$, когда нам нужно использовать многочлены, степени не более $2 n - 1$. Определим стратегию уменьшения степени:

  Если итоговый $n = 2m$, то с помощью ядра $J_m$ построим рассмотренный выше тригонометрический многочлен, иначе $n = 2m + 1$, для которого также построим требуемый $J_m$. Таким образом,
  #eq[
    $norm(f - T) < (C M) / (2 m) < (C M) / n$
  ]
  Пусть теперь теорема доказана для произвольного $r$ и более того, если интеграл по периоду равен нулю, то и полученная апроксимация удовлетворяет этому свойству.

  Докажем, что тогда то же выполнено и для $r + 1$. Пусть $f in W^(r + 1) (M)$. Тогда $f' in W^r (M)$. Причём, очевидно, интеграл по периоду от функции $f'$ равен нулю.

  Тогда, согласно индукционному предположению, существует $T(x) in cal(T)_(2 n - 1)$, для которого выполнено неравенство $norm(f' - T) < C^r m n^(-r)$ и интеграл по периоду от $T$ равен нулю.

  Тогда свободный член тригонометрического многочлена $T$ нулевой. Поэтому существует тригонометрический многочлен $U$ той же степени с нулевым свободный членом, для которого $U' = T$. Следовательно
  #eq[
    $norm((f - U)') = norm(f' - T) < C^r M n^(-r)$
  ]
  Поэтому $t - U in W^1 (C^r M n^(-r))$. Следовательно, существует $t in cal(T)_(2 n - 1)$, такой, что
  #eq[
    $norm((f - U) - t) < C(C^r M n^(-r)) / n = C^(r + 1) M / n^(r + 1)$
  ]
  Причём, если интеграл по периоду функции $f$ равен нулю, то это же справедливо и для многочлена $U + t in cal(T)_(2 n - 1)$.
]

#pagebreak()
