#include<bits/stdc++.h>
using namespace std;
typedef int ll;
typedef long long int li;
const ll MAXN=3e5+51,MOD=998244353,G=3,INVG=332748118,I=86583718;
ll fd,type;
ll f[MAXN],res[MAXN],rev[MAXN];
inline ll read()
{
    register ll num=0,neg=1;
    register char ch=getchar();
    while(!isdigit(ch)&&ch!='-')
    {
        ch=getchar();
    }
    if(ch=='-')
    {
        neg=-1;
        ch=getchar();
    }
    while(isdigit(ch))
    {
        num=(num<<3)+(num<<1)+(ch-'0');
        ch=getchar();
    }
    return num*neg;
}                                 
inline ll qpow(ll base,ll exponent)
{
    li res=1;
    while(exponent)
    {
        if(exponent&1)
        {
            res=(li)res*base%MOD;
        }
        base=(li)base*base%MOD,exponent>>=1;
    }
    return res;
}
inline void NTT(ll *cp,ll cnt,ll inv)
{
    ll cur=0,res=0,omg=0;
    for(register int i=0;i<cnt;++i)
    {
        if(i<rev[i])
        {
            swap(cp[i],cp[rev[i]]);
        }
    }
    for(register int i=2;i<=cnt;i<<=1)
    {
        cur=i>>1,res=qpow(inv==1?G:INVG,(MOD-1)/i);
        for(register ll *p=cp;p!=cp+cnt;p+=i)
        {
            omg=1;
            for(register int j=0;j<cur;++j)
            {
                ll t=(li)omg*p[j+cur]%MOD,t2=p[j];
                p[j+cur]=(t2-t+MOD)%MOD,p[j]=(t2+t)%MOD;
                omg=(li)omg*res%MOD;
            }
        }
    }
    if(inv==-1)
    {
        ll invl=qpow(cnt,MOD-2);
        for(register int i=0;i<=cnt;++i)
        {
            cp[i]=(li)cp[i]*invl%MOD;
        }
    }
}
inline void deriv(ll fd,ll *f,ll *res)
{
    for(register int i=1;i<fd;++i)
    {
        res[i-1]=(li)f[i]*i%MOD;
    }
    res[fd-1]=0;
}
inline void integ(ll fd,ll *f,ll *res)
{
    for(register int i=1;i<fd;++i)
    {
        res[i]=(li)f[i-1]*qpow(i,MOD-2)%MOD;
    }
    res[0]=0;
}
inline void inv(ll fd,ll *f,ll *res)
{
    static ll tmp[MAXN];
    if(fd==1)
    {
        res[0]=qpow(f[0],MOD-2);
        return;
    }
    inv((fd+1)>>1,f,res);
    ll cnt=1,limit=-1;
    while(cnt<(fd<<1))
    {
        cnt<<=1,limit++;
    }
    for(register int i=0;i<cnt;++i)
    {
        tmp[i]=i<fd?f[i]:0;
        rev[i]=(rev[i>>1]>>1)|((i&1)<<limit);
    }
    NTT(tmp,cnt,1),NTT(res,cnt,1);
    for(register int i=0;i<cnt;++i)
    {
        res[i]=(li)(2-(li)tmp[i]*res[i]%MOD+MOD)%MOD*res[i]%MOD;
    }
    NTT(res,cnt,-1);
    for(register int i=fd;i<cnt;++i)
    {
        res[i]=0;
    }
}
inline void ln(ll fd,ll *f,ll *res)
{
    static ll pinv[MAXN],der[MAXN];
    ll cnt=1,limit=-1;
    while(cnt<(fd<<1))
    {
        cnt<<=1,limit++;
    }
    inv(fd,f,pinv),deriv(fd,f,der);
    for(register int i=0;i<cnt;++i)
    {
        rev[i]=(rev[i>>1]>>1)|((i&1)<<limit);
    }
    NTT(pinv,cnt,1),NTT(der,cnt,1);
    for(register int i=0;i<cnt;++i)
    {
        der[i]=(li)der[i]*pinv[i]%MOD;
    }
    NTT(der,cnt,-1),integ(fd,der,res);
    for(register int i=0;i<cnt;++i)
    {
        der[i]=pinv[i]=0;
    }
}
inline void exp(ll fd,ll *f,ll *res)
{
    static ll texp[MAXN];
    if(fd==1)
    {
        res[0]=1;
        return;
    }
    ll cnt=1,limit=-1;
    while(cnt<(fd<<1))
    {
        cnt<<=1,limit++;
    }
    exp((fd+1)>>1,f,res),ln(fd,res,texp);
    for(register int i=0;i<cnt;++i)
    {
 		rev[i]=(rev[i>>1]>>1)|((i&1)<<limit);
    }
    texp[0]=(f[0]+1-texp[0]+MOD)%MOD;
    for(register int i=1;i<fd;++i)
    {
        texp[i]=(f[i]-texp[i]+MOD)%MOD;
    }
    NTT(texp,cnt,1),NTT(res,cnt,1);
    for(register int i=0;i<cnt;++i)
    {
        res[i]=(li)res[i]*texp[i]%MOD;
    }
    NTT(res,cnt,-1);
    for(register int i=0;i<cnt;++i)
    {
        texp[i]=0,res[i]=i<fd?res[i]:0;
    }
}
// type = 0 is sin, type = 1 is cos
inline void trig(ll fd,ll *f,ll *res,ll type)
{
    ll inv2=499122177,inv2i=qpow(I<<1,MOD-2);
    static ll tmp[MAXN],tmp2[MAXN],texp[MAXN],texp2[MAXN];
    for(register int i=0;i<fd;i++)
    {
        tmp[i]=(li)I*f[i]%MOD,tmp2[i]=MOD-tmp[i];
    }
    exp(fd,tmp,texp),exp(fd,tmp2,texp2);
    for(register int i=0;i<fd;i++)
    {
        res[i]=type?(texp[i]+texp2[i])%MOD:(texp[i]-texp2[i]+MOD)%MOD;
        res[i]=(li)res[i]*(type?inv2:inv2i)%MOD;
    }
}
int main()
{
    fd=read(),type=read();
    for(register int i=0;i<fd;++i)
    {
        f[i]=read();
    }
    trig(fd,f,res,type);
    for(register int i=0;i<fd;++i)
    {
        printf("%d ",res[i]);
    }
}
