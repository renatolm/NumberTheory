import Mathlib

-- Mostre que 1 + x + x^2 + ... + x^{n-1} = (x^n -1)/(x - 1)


--################################################################
-- Se a, b e c são inteiros, a|b e b|c, então a|c


--################################################################
-- Se a, b, c, m e n são inteiros, c|a e c|b então c|(m*a + n*b)


--################################################################
-- (Algoritmo da divisão)
-- Dados dois inteiros a e b, b>0, existe um único par de inteiros q e r tais que
-- a=q*b + r, com 0<=r<b   (r=0 <=> b|a)
-- (q é chamado de quociente e r de resto da divisão de a por b)


--################################################################
-- Def: o máximo divisor comum de dois inteiros a e b, denotado por (a,b), é o maior inteiro que divide a e b.

-- Seja d o máximo divisor comum de a e b, então existem inteiros n_0 e m_0 tais que d = n_0*a + m_0*b


--################################################################
-- O máximo divisor comum d de a e b é o divisor positivo de a e b o qual é divisível por todo divisor comum


--################################################################
-- Para todo inteiro positivo t, (t*a, t*b) = t*(a,b)


--################################################################
-- Se c>0 e a e b são divisíveis por c, então
-- (a/c, b/c) = 1/c * (a,b)


--################################################################
-- Se (a,b) = d, temos que (a/d, b/d) = 1


--################################################################
-- Def: Os inteiros a e b são relativamente primos quando (a,b) = 1

-- Para a,b e x inteiros temos (a,b) = (a,b + a*x)


--################################################################
-- Se a|b*c e (a,b)=1 então a|c


--################################################################
-- Se a e b são inteiros e a=q*b+r onde q e r são inteiros, então (a,b) = (b,r)
