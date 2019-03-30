
def M(n):
    print(n, end=" ")  # for debugging
    
    if n > 100:
        return n - 10
    else:
        return M(M(n + 11))
    
    
if __name__ == '__main__':
    n = 99
    print("!-", M(n), "-!", sep="")