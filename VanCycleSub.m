function [Dim,  Tlvc, U, W, CoeffNonZero]=VanCycleSub(d,e,rowi,colj)
%% USAGE:   
%%          [Dim, U, W, Tlvc, CoeffNonZero, Ured, Wred]=VanCycleSub(d,e,rowi,colj)
%%                           d,e,rowi,colj integer numbers. d,e>1
%% PURPOSE: 
%%          Compute the subspace spanned by the monodromy action of 
%%          the fibration given by:
%%              f:=x^d+y^e,   acting on the vanishing cycle in the 
%%           position (rowi,colj) of the Dinkin diagram. 
%% RETURN:  
%%          - Dim: is the number of diferent eigenvalues of the monodromy 
%%          matrix. 
%%          - Tlvc: is a matrix in which each column represents a vector 
%%          of lemma 2.5 in [1]. The first column represent the vanishing
%%          in the position (rowi, colj).
%%          - U: is the basis of the eigenvector of the monodromy matrix.
%%          Each column of U is an eigenvector of the monodromy matix.
%%          - W: satifys UW=Tlvc. Thus, each column are the coefficients
%%          of the equation Sum_i c_ij U_i=Tlvc_j. 
%%          - CoeffNonZero: are the coefficients different from zero. In 
%%          each column there are the non zero coeffecients associated to
%%          to the columns of Tlvc.
%% NOTE:
%%          1) If all critical values are different, then Dim=(d-1)(e-1).
%%          2) In order to determine wich coefficients are 0 is neccesary 
%%          to use round. The number of decimals in used in the round 
%%          function is "Rzeros". This integer number is by 
%%          Rzeros=-round(log10(max(aW(:,1))))+3, where aW=abs(W). 
%%          The number 3 in this expression Could be changed if more
%%          precision was needed.
%%          3) We can define a reduced basis Ured:
%%          Ured=zeros(size(U,1),size(CoeffNonZero,1));
%%          Ured=U(:,CoeffNonZero(:,1));  
%%          and a reduced matrix of coefficients Wred:
%%          Wred=zeros(size(CoeffNonZero,1),size(W,5));
%%          Wred=W(CoeffNonZero(:,1),:);
%%          with the eigenvector whic appear in the representation of the
%%          vanishing cycle in the position (rowi,colj).
%%          These reduced expressions also satisfies Ured*Wred=Tlvc.
%%
%% SEE ALSO: 
%%          MonMatrix, Proof_lemma_2_5
%% EXAMPLE_: 
%%          [Dim, Tlvc U, W, CoeffNonZero]=VanCycleSub(6,8,3,4);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Computing the monodromy matrix.
Im=MonMatrix([d,e],1);    
N=size(Im,1);

%% Computing the Krylov space dimension
[U, Diag]=eig(Im);
Diag=unique(round(diag(Diag),10));  %%%% Different eigenvalues of the Intersection matrix
Dim=length(Diag);

if Dim == N
   p=gcd(d,colj);
   r=gcd(e,rowi);
   %% The position of the vanishing cycle
   L=(e-1)*(colj-1)+rowi;

   %% Theoreic Vanishing cycles in the subspaces generated. They are in the columns of the Dynkin diagram, rn with n=1...d/r-1
    Tvci=zeros(N,1);   %% Conditions by fixing i
    Cont=1;
    for mm=1:d/p-1
        %% v_{i,mp}
        Dij=(mm*p-1)*(e-1)+rowi; % from ij to position in the Dynkin
        Tvci(Dij,Cont)=1;
        Cont=Cont+1;
    end

    for kk=1:p-1
         %% v_{i,mp-k}+v_{i,mp+k}
         Dij=((colj-kk)-1)*(e-1)+rowi; % from ij to position in the Dynkin
         Tvci(Dij,Cont)=1; 
         Dij=((colj+kk)-1)*(e-1)+rowi; % from ij to position in the Dynkin
         Tvci(Dij,Cont)=1; 
         Cont=Cont+1;

         %% v_{i-1,mp-k}+v_{i-1,mp+k}+v_{i+1,mp-k}+v_{i+1,mp+k}
         Dij=((colj-kk)-1)*(e-1)+(rowi-1); % from ij to position in the Dynkin
         if rowi-1<e && rowi-1>0 Tvci(Dij,Cont)=1; end
         Dij=((colj+kk)-1)*(e-1)+(rowi-1); % from ij to position in the Dynkin
         if rowi-1<e && rowi-1>0 Tvci(Dij,Cont)=1; end
         Dij=((colj-kk)-1)*(e-1)+(rowi+1); % from ij to position in the Dynkin
         if rowi+1<e && rowi+1>0 Tvci(Dij,Cont)=1; end
         Dij=((colj+kk)-1)*(e-1)+(rowi+1); % from ij to position in the Dynkin
         if rowi+1<e && rowi+1>0 Tvci(Dij,Cont)=1; end
         Cont=Cont+1;
    end


    Tvcj=zeros(N,1);   %% Conditions by fixing j
    Cont=1;
    for nn=1:e/r-1
        %% v_{nr,j}
        Dij=(colj-1)*(e-1)+nn*r; % from ij to position in the Dynkin
        Tvcj(Dij,Cont)=1; Cont=Cont+1;
    end
    for ll=1:r-1
         %% v_{nr-l,j}+v_{nr+l,j}
         Dij=(colj-1)*(e-1)+(rowi-ll); % from ij to position in the Dynkin
         Tvcj(Dij,Cont)=1;
         Dij=(colj-1)*(e-1)+(rowi+ll); % from ij to position in the Dynkin
         Tvcj(Dij,Cont)=1; Cont=Cont+1;

          %% v_{nr-l,j-1}+v_{nr+l,j-1}+v_{nr-l,j+1}+v_{nr+l,j+1}
         Dij=((colj-1)-1)*(e-1)+(rowi-ll); % from ij to position in the Dynkin
         if colj-1<d && colj-1>0 Tvcj(Dij,Cont)=1; end
         Dij=((colj-1)-1)*(e-1)+(rowi+ll); % from ij to position in the Dynkin
         if colj-1<d && colj-1>0 Tvcj(Dij,Cont)=1; end
         Dij=((colj+1)-1)*(e-1)+(rowi-ll); % from ij to position in the Dynkin
         if colj+1<d && colj+1>0 Tvcj(Dij,Cont)=1; end
         Dij=((colj+1)-1)*(e-1)+(rowi+ll); % from ij to position in the Dynkin
         if colj+1<d && colj+1>0 Tvcj(Dij,Cont)=1; end
    end


   %%%% Choosing the vanishing cycles described in Lemma 2.5
   vL=zeros(N,1); vL(L)=1;
   Tlvc=[vL Tvci Tvcj]; %%% The union of two conditions
   [~, pivots]=rref(Tlvc);
   Tlvc=Tlvc(:,pivots);
   
   %%%% The solutions of U*x=Tlvc
   W=U\Tlvc;    
   %% U*x=Tlvc(:,1) are the generators Krylov sub. of v_(rowi,colj)
   aW=abs(W); %% The norm of W
   
   Rzeros=-round(log10(max(aW(:,1))))+3; %% The order of rounding to zero
   if Rzeros <4
       Rzeros=4;
   end

   [IndR, IndC]=find(round(aW(:,:),Rzeros)~=0); %% The coeff. different to 0
   CoeffNonZero=zeros(length(IndR(IndC==1)),1);
   for k=1:size(Tlvc,2)
       CoeffNonZero(1:length(IndR(IndC==k)),k)=[IndR(IndC==k)];
   end
else
   Tlvc=0; U=0; W=0; CoeffNonZero=0;
end

