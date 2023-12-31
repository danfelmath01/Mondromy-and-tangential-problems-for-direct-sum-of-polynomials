function Im=MonMatrix(m, ch) 
%% USAGE:   
%%        Im=MonMatrix(vector_expression,int_expression); m(j)>=2, ch=0 or 1
%% PURPOSE: 
%%        Compute the monodromy matrix of polynomial:
%%              f:=x_1^m[1]+x_2^m[2]+...+x_{n+1}^m[n+1].
%%       This matrix is in the basis of D. Lopez Garcia's thesis Section 3.3. 
%%           
%% RETURN:  
%%          If ch=0, then return intersection matrix Im. 
%%          If ch!=0, then return monodromy matrix Im
%%          (see Picard-Lefschetz formula).  
%% SEE ALSO: 
%%           VanCylcesSub
%% EXAMPLE_: 
%%           m0=[6,4];
%%           Im=MonMatrix(m0, 0)

if min(size(m))>1
    fprintf('m should be a vector');
    Im=0;
else
if min(m)<2
    fprintf('Each m(i) should be greater than 1');
    Im=0;
else

ms=m-1;           % Number of critical points in any variable.
n=length(m)-1;    % Dimension of the fiber (Number of variables-1).
h=floor((ms)/2); % Number of negative critical values in each coordinate.
M=max(m);         % Maximum degree.
L=prod(ms);      % Rank of the homology group.

%% Matrix of Index of each variable:
for i=1:n+1     
    for j=1:m(i)/2
        I(2*j-1,i)=h(i)+j;   %Matrix of Index of each variable.
        if 2*j<=m(i)-1
           I(2*j,i)=j; 
        end
    end
end

for i=1:L
    for j=1:L
            Ni=i-1; Nj=j-1;
            for k=1:n+1
                % Define the beta and beta' acording to: 
                % Ni=a_1(Pi_j>1(m_j-1))+a_2(Pi_j>2(m_j-1))+..., ak<m_k-1
                ni=floor(Ni/prod(ms(k+1:end)));
                nj=floor(Nj/prod(ms(k+1:end)));
                Ni=Ni-ni*prod(ms(k+1:end));
                Nj=Nj-nj*prod(ms(k+1:end));
                Bi(k)=I(ni+1,k); Bj(k)=I(nj+1,k); 
                Bcompa(k)=((Bi(k)+h(k)==Bj(k) | Bi(k)+h(k)+1==Bj(k)) & Bi(k)<=h(k) & Bj(k)>h(k)) | (Bi(k)==Bj(k)); % Comparison between betas
                Bexp(k)=(Bi(k)~=Bj(k)); %% B exponent: Apport a sign if the values of betas in posiction k are differents.
            end
            if (i~= j && prod(Bcompa))
                Im(i,j)=(-1)*(-1)^(n*(n-1)/2)*(-1)^(sum(Bexp));
                Im(j,i)=(-1)^n*Im(i,j);
            elseif i==j
                Im(i,j)=(-1)^(n*(n-1)/2)*(1+(-1)^n);
            end
    end
end
if ch~=0 %% The oupout is the monodromy matrix
    Im=eye(L)+(-1)^((n*(n-1))/2)*Im; %% Picard-Lefschetz formula
end
end
end



