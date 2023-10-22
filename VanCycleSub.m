function [Dim, Wout,Vout]=VanCycleSub(m,accuracy)
%% USAGE:   
%%          [Dim, Wout,Vout]=VanCyclesSub(vector_expression); m(j)>=2. 
%%                           accuracy is the round order: 10^{-accuary}=0
%% PURPOSE: 
%%          Compute the subspace spanned by the monodromy action of 
%%          the fibration given by:
%%              f:=x_1^m[1]+x_2^m[2]+...+x_{n+1}^m[n+1],
%%          acting on each vanishing cycle. 
%% RETURN:  
%%          - Dim: is the number of diferent eigenvalues of the monodromy 
%%          matrix. 
%%          - Wout(:,:,j): is the  subspace generated by the monodromy action
%%          on the vanisihg cycle v_j=(0 0... 0 1 0...0).
%%          - Vout: In the column j, are the vanishing cycle in the space 
%%          generated by v_j.
%% NOTE:
%%          If all critical values are different, then the rank of 
%%          Wout(:,:,j) is equal to the dimension of the Krylov space 
%%          of the vector v_j  and the monodromy matrix 
%%          (see D. Lopez Garcia's thesis Section 3.3. ). 
%%          Else, Wout is returned with 0.
%% SEE ALSO: 
%%          MonMatrix
%% EXAMPLE_: 
%%           m0=[6,4];
%%           [Dim, Wout,Vout]=VanCycleSub(m0)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Computing the intersection matrix.
Im=MonMatrix(m,1);    
N=size(Im,1);

%% Computing the Krylov space dimension
[U Diag]=eig(Im);
Diag=unique(round(diag(Diag),accuracy));  %%%% Different eigenvalues of the Intersection matrix
Dim=length(Diag);

if Dim == N
   %W=round(inv(U),10);  %% U*W(:,k)=v_k, the cannonical vector.
   W=inv(U);
   Wout=zeros(N);
   for k=1:N
      %% Look for the eigen vector in the representation of v_k, with coefficients equal to 0:	
      Ind=find(round(W(:,k),accuracy)~=0); 

      %% Choose the eigen-vectors which generate the image of v_k 	
      Ur=U(:,Ind);

      %% Compute the subspace spanned by the columns of Vr, in the cannonical basis: 
      Wr=round((Ur*W(Ind,:)),accuracy); 
      Wout(1:size(Wr,1), 1:size(Wr,2),k)=Wr; %% Any matrix Wout(:,:,k) is the subspace generated by e_k.
       
      %% Look for the vanishing cyles in the image:
      Ind1=find(round(sum(abs(Wr)),5)==1);   %%% Find the elements which has only a vanishing cycle in the represetation
      [Uc,Jnd1]=find(round(Wr(:,Ind1),5)==1);  %%% Find the correspond row to the vanishing cycle in the representation
      Vout(1:size(Uc,1),k)=sort(Uc);
   end 
else
   Wout=zeros(N);
   for k=1:N   
      Wout(:,:,k)=zeros(N);
   end
      Vout=0;
end
end

