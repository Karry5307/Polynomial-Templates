// luogu-judger-enable-o2
#include<bits/stdc++.h>
using namespace std;
typedef int ll;
typedef long long int li;
const ll MAXN=131081,MOD=998244353,G=3,INVG=332748118;
ll fd,pcnt;
ll f[MAXN>>1],pts[MAXN>>1],res[MAXN>>1],rev[MAXN];
char sw[32];
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
inline void write(ll x,char ch=' ')
{
    ll tp=0;
    while(x)
    {
        sw[++tp]=x%10+'0',x/=10;
    }
    while(tp)
    {
        putchar(sw[tp--]);
    }
    putchar(ch);
}
inline ll qpow(ll base,ll exponent)
{
    li res=1;
    while(exponent)
    {
        if(exponent&1)
        {
            res=1ll*res*base%MOD;
        }
        base=1ll*base*base%MOD,exponent>>=1;
    }
    return res;
}
inline void NTT(ll *cp,ll cnt,ll inv)
{
    ll cur=0,res=0,omg=0;
    for(register int i=0;i<cnt;i++)
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
            for(register int j=0;j<cur;j++)
            {
                ll t=1ll*omg*p[j+cur]%MOD,t2=p[j];
                p[j+cur]=(t2-t+MOD)%MOD,p[j]=(t2+t)%MOD;
                omg=1ll*omg*res%MOD;
            }
        }
    }
    if(inv==-1)
    {
        ll invl=qpow(cnt,MOD-2);
        for(register int i=0;i<=cnt;i++)
        {
            cp[i]=1ll*cp[i]*invl%MOD;
        }
    }
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
    for(register int i=0;i<cnt;i++)
    {
        tmp[i]=i<fd?f[i]:0;
        rev[i]=(rev[i>>1]>>1)|((i&1)<<limit);
    }
    NTT(tmp,cnt,1),NTT(res,cnt,1);
    for(register int i=0;i<cnt;i++)
    {
        res[i]=1ll*(2-1ll*tmp[i]*res[i]%MOD+MOD)%MOD*res[i]%MOD;
    }
    NTT(res,cnt,-1);
    for(register int i=fd;i<cnt;i++)
    {
        res[i]=0;
    }
}
inline void mod(ll fd,ll gd,ll *f,ll *g,ll *r)
{
    static ll tmpf[MAXN],tmpg[MAXN],tinv[MAXN],q[MAXN];
    if(fd<gd)
    {
    	for(register int i=0;i<gd-1;i++)
    	{
    		r[i]=f[i];
        }
        return;
    }
    for(register int i=0;i<fd;i++)
    {
        tmpf[i]=f[fd-1-i];
    }
    for(register int i=0;i<gd;i++)
    {
        tmpg[i]=g[gd-1-i];
    }
    inv(fd-gd+2,tmpg,tinv);
    ll cnt=1,limit=-1;
    while(cnt<(fd<<1))
    {
        cnt<<=1,limit++;
    }
    for(register int i=0;i<cnt;i++)
    {
       rev[i]=(rev[i>>1]>>1)|((i&1)<<limit);
    }
    NTT(tmpf,cnt,1),NTT(tinv,cnt,1);
    for(register int i=0;i<cnt;i++)
    {
    	q[i]=1ll*tmpf[i]*tinv[i]%MOD;
    }
    NTT(q,cnt,-1),reverse(q,q+fd-gd+1);
    for(register int i=0;i<cnt;i++)
    {
        tmpf[i]=tinv[i]=tmpg[i]=0;
        q[i]=i<fd-gd+1?q[i]:0,g[i]=i<gd?g[i]:0;
    }
    cnt>>=1,limit--;
    for(register int i=0;i<cnt;i++)
    {
       rev[i]=(rev[i>>1]>>1)|((i&1)<<limit);
    }
    NTT(q,cnt,1),NTT(g,cnt,1);
    for(register int i=0;i<cnt;i++)
    {
        tmpf[i]=1ll*q[i]*g[i]%MOD;
    }
    NTT(g,cnt,-1),NTT(tmpf,cnt,-1);
    for(register int i=0;i<gd-1;i++)
    {
        r[i]=(f[i]-tmpf[i]+MOD)%MOD;
    }
    for(register int i=0;i<cnt;i++)
    {
        q[i]=tmpf[i]=0;
    }
}
vector<ll> tmpf2[MAXN<<2];
void dnc(ll *pts,ll l,ll r,ll node)
{
    static ll tmp[MAXN],tmp2[MAXN];
    if(l==r)
    {
        tmpf2[node].push_back((MOD-pts[l])%MOD),tmpf2[node].push_back(1);
        return;
    }
    ll mid=(l+r)>>1,ls=node<<1,rs=ls|1;
    dnc(pts,l,mid,ls),dnc(pts,mid+1,r,rs);
    ll d=tmpf2[ls].size(),d2=tmpf2[rs].size();
    for(register int i=0;i<d;i++)
    {
        tmp[i]=tmpf2[ls][i];
    }
    for(register int i=0;i<d2;i++)
    {
        tmp2[i]=tmpf2[rs][i];
    }
    ll cnt=1,limit=-1;
    while(cnt<(d+d2))
    {
        cnt<<=1,limit++;
    }
    for(register int i=0;i<cnt;i++)
    {
       rev[i]=(rev[i>>1]>>1)|((i&1)<<limit);
    }
    NTT(tmp,cnt,1),NTT(tmp2,cnt,1);
    for(register int i=0;i<cnt;i++)
    {
    	tmp[i]=1ll*tmp[i]*tmp2[i]%MOD;
    }
    NTT(tmp,cnt,-1);
    for(register int i=0;i<d+d2-1;i++)
    {
        tmpf2[node].push_back(tmp[i]);
    }
    for(register int i=0;i<cnt;i++)
    {
        tmp[i]=tmp2[i]=0;
    }
};
ll tmpf3[17][MAXN];
void dnc2(ll fd,ll *f,ll depth,ll l,ll r,ll node,ll *res)
{
    static ll tmp[MAXN],pw[17];
    if(r-l<=1024)
    {
        for(register int i=l;i<=r;i++)
        {
            ll x=pts[i],cur=f[fd-1],v1,v2,v3,v4;
            pw[0]=1;
            for(register int j=1;j<=16;j++)
            {
                pw[j]=1ll*pw[j-1]*x%MOD;
            }
            for(register int j=fd-2;j-15>=0;j-=16)
            {
                v1=(1ll*cur*pw[16]+1ll*f[j]*pw[15]+
                    1ll*f[j-1]*pw[14]+1ll*f[j-2]*pw[13])%MOD;
                v2=(1ll*f[j-3]*pw[12]+1ll*f[j-4]*pw[11]+
                    1ll*f[j-5]*pw[10]+1ll*f[j-6]*pw[9])%MOD;
                v3=(1ll*f[j-7]*pw[8]+1ll*f[j-8]*pw[7]+
                    1ll*f[j-9]*pw[6]+1ll*f[j-10]*pw[5])%MOD;
                v4=(1ll*f[j-11]*pw[4]+1ll*f[j-12]*pw[3]+
                    1ll*f[j-13]*pw[2]+1ll*f[j-14]*pw[1])%MOD;
                cur=(0ll+v1+v2+v3+v4+f[j-15])%MOD;
            }
            for(register int j=((fd-1)&15)-1;~j;j--)
            {
                cur=(1ll*cur*x+f[j])%MOD;
            }
            res[i]=cur;
        }
        return;
    }
    ll sz=tmpf2[node].size()-1;
    for(register int i=0;i<sz+1;i++)
    {
        tmp[i]=tmpf2[node][i];
    }
    mod(fd,sz+1,f,tmp,tmpf3[depth]);
    ll mid=(l+r)>>1;
    dnc2(sz,tmpf3[depth],depth+1,l,mid,node<<1,res);
    dnc2(sz,tmpf3[depth],depth+1,mid+1,r,(node<<1)|1,res);
    for(register int i=0;i<sz;i++)
    {
        tmpf3[depth][i]=0;
    }
}
inline void eval(ll fd,ll pcnt,ll *f,ll *pts,ll *res)
{
    dnc(pts,0,pcnt-1,1),dnc2(fd,f,0,0,pcnt-1,1,res);
}
int main()
{
    fd=read()+1,pcnt=read();
    for(register int i=0;i<fd;i++)
    {
        f[i]=read();            
    }
    for(register int i=0;i<pcnt;i++)
    {
        pts[i]=read();
    }
    eval(fd,pcnt,f,pts,res);
    for(register int i=0;i<pcnt;i++)
    {
        write(res[i],'\n');
    }
}
