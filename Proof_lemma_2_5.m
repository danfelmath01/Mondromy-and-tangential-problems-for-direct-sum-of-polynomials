function [Proof, FailVanCycle]=Proof_lemma_2_5(d,e)
%% USAGE:   
%%          [Proof, FailVanCycle]=Proof_lemma_2_5(d,e);  
%%                    d,e integer number associated with x^d+y^e
%%                        d,e>1
%% PURPOSE: 
%%          Compute the subspace spanned by the monodromy action of 
%%          the fibration given by:
%%              f:=x^d+y^e,   acting on the each vanishing cycle.
%%          Proof of lemma 2.5 for d,e  given.
%% RETURN:  
%%          - Proof: It's a logical value. 1 means that the lemma 2.5 is 
%%           true for the given d,e.
%%           0 means that the lemma fail for the given d,e for some 
%%           vanishing cycles.
%%          - FailVanCycle: If Proof=0, then FailVanCycle is a list of 
%%            the vanishing cycles for which the lemma 2.5 is not true.
%% NOTE:
%%          Let d,e>1 such that gcd(d,e)>2. If the lemma is "not true" 
%%          for d,e, the rounding function used to determine whether 
%%          a coefficient is zero must be checked. To do this the 
%%          FailVanCycle list would be useful.
%% SEE ALSO: 
%%          MonMatrix, VanCycleSub
%% EXAMPLE_: 
%%         [Proof, FailVanCycle]=Proof_lemma_2_5(6,8);
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Computing the intersection matrix.
Im=MonMatrix([d,e],1);   
FailVanCycle=0; kkk=1;

%% Computing the Krylov space dimension
[U, Diag]=eig(Im);
Diag=unique(round(diag(Diag),10));  %%%% Different eigenvalues of the Intersection matrix
Dim=length(Diag);

%%%%%%%%
N=(e-1)*(d-1);


%%% Proof of Lemma 2.5
if N==Dim %% If the eigenvalues are different
   Proof_for_d=1;   %%%%This is the product os logic sentence for any degre d.
   for l=1:N 
        %% First we identify the column and the row in the Dynkin diagram
        colj=ceil(l/(e-1));
        rowi=mod(l,(e-1)); if rowi==0 rowi=e-1; end
        p=gcd(d,colj);
        r=gcd(e,rowi);

        %% Theoreic Vanishing cycles in the subspaces generated. 
        %They are in the columns of the Dynkin diagram, rn with n=1...d/r-1
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
       vL=zeros(N,1); vL(l)=1;
       Tlvc=[vL Tvci Tvcj]; %%% The union of two conditions
       
       %%%% The solutions of U*x=Tlvc
       W=U\Tlvc;    
       %% U*x=Tlvc(:,1) are the generators Krylov sub. of vl
        aW=abs(W); %% The norm of W
       Rzeros=-round(log10(max(aW(:,1))))+3; %% The order of rounding to zero
       if Rzeros <4
           Rzeros=4;
       end
      
       [IndR, IndC]=find(round(aW(:,:),Rzeros)~=0); %% The coeff. different to 0
       Proof_for_vl=1;
       if length(IndR(IndC==1))~=N
           for k=1:size(Tlvc,2)
               Proof_for_vl=Proof_for_vl*prod(ismember(IndR(IndC==k),IndR(IndC==1)));
           end
       end
       if Proof_for_vl==0
           FailVanCycle(kkk)=l;
           kkk=kkk+1;
       end

       Proof_for_d=Proof_for_d*Proof_for_vl;
   end
   Proof=Proof_for_d;
else %% If there are eigenvalues with multiplicity bigger than 1
   Proof=0;
end
         