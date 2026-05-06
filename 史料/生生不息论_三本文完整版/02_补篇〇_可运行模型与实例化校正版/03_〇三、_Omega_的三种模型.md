## 〇三、$\Omega$ 的三种模型

设：

$$
x=(U,A,R,T),\qquad x_j\in[0,1]
$$

### 一、短板模型 $\Omega_{\min}$

$$
\Omega_{\min}(x):=\min(U,A,R,T)
$$

用处：高风险场景。任何一维失败都足以使开失败。

性质：

1. 单调；
2. 强短板敏感；
3. 可解释；
4. 对假繁荣、假自由、假多选项最保守。

### 二、几何模型 $\Omega_{\mathrm{geo}}$

给权重：

$$
\alpha_U+\alpha_A+\alpha_R+\alpha_T=1,\qquad \alpha_j>0
$$

定义：

$$
\Omega_{\mathrm{geo}}(x)
:=
U^{\alpha_U}A^{\alpha_A}R^{\alpha_R}T^{\alpha_T}
$$

若任一分量为 $0$，则全值为 $0$。  
用处：常规治理、系统设计、制度评估。

### 三、护栏均值模型 $\Omega_{\mathrm{guard}}$

先取短板：

$$
m(x):=\min(U,A,R,T)
$$

再取加权均值：

$$
\bar{x}_{\alpha}:=\alpha_UU+\alpha_AA+\alpha_RR+\alpha_TT
$$

定义：

$$
\Omega_{\mathrm{guard}}(x)
:=
m(x)^{\beta}\bar{x}_{\alpha},
\qquad
\beta\ge1
$$

用处：允许局部优势有贡献，但仍防止“一项归零仍称强开”。

### 选模律

$$
\mathcal{M}_{\Omega}\in
\{
\Omega_{\min},
\Omega_{\mathrm{geo}},
\Omega_{\mathrm{guard}}
\}
$$

选模须写入审校记录：

$$
\mathsf{Audit}.\mathsf{omegaModel}:=\mathcal{M}_{\Omega}
$$

若三模型结论冲突，则：

$$
\mathrm{判定}=\mathsf{U}
\quad\text{或}\quad
\mathrm{判定}=\mathrm{需更高审校}
$$

高风险场景默认采用 $\Omega_{\min}$。

