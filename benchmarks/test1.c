int fib(int n){
    if (n<=1){
        return 0;
    } 
    else{
        int y= fib(n-1);
        int z= fib(n-2);
        int x= y+z;
        return x;
    }
}
int main(){
    fib(7);
    return 0;
}