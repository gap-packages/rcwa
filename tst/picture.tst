#############################################################################
##
#W  picture.tst                GAP4 Package `RCWA'                Stefan Kohl
##
##  This file contains tests of RCWA's functionality for bitmap graphics
##  files in general, and for drawing pictures of orbits of rcwa groups in
##  particular.
##
#############################################################################

gap> START_TEST( "picture.tst" );
gap> RCWADoThingsToBeDoneBeforeTest();
gap> dir := DirectoryTemporary();;
gap> pic_colored := RandomMat(30,40,[0..2^24-1]);;
gap> filename := Filename(dir,"random1.bmp");;
gap> SaveAsBitmapPicture(pic_colored,filename);
gap> pic_colored2 := LoadBitmapPicture(filename);;
gap> pic_colored2 = pic_colored;
true
gap> pic_bw := RandomMat(40,60,GF(2));;
gap> filename := Filename(dir,"random2.bmp");;
gap> SaveAsBitmapPicture(pic_bw,filename);
gap> pic_bw2 := LoadBitmapPicture(filename);;
gap> pic_bw2 = pic_bw;
true
gap> R := Integers^2;
( Integers^2 )
gap> S := Union(2*R,5*R+[1,3]);
<union of 28 residue classes (mod (10,0)Z+(0,10)Z)>
gap> filename := Filename(dir,"grid.bmp");;
gap> DrawGrid(S,[-50..50],[-50..50],filename);
gap> PSL2Z := Image(IsomorphismRcwaGroup(FreeProduct(CyclicGroup(2),
>                                                    CyclicGroup(3))));;
gap> DrawOrbitPicture(PSL2Z,[0,1],20,512,512,false,fail,
>                     Filename(dir,"example1.bmp"));
gap> DrawOrbitPicture(PSL2Z,Combinations([1..4],2),20,512,512,true,
>                     [[255,0,0],[0,255,0],[0,0,255]],
>                     Filename(dir,"example2.bmp"));
gap> DrawOrbitPicture(PSL2Z,[0,1],20,256,256,true,
>                     [[255,0,0],[0,255,0],[0,0,255]],
>                     Filename(dir,"example3.bmp"));
gap> G := Image(IsomorphismRcwaGroup(FreeProduct(CyclicGroup(3),
>                                                CyclicGroup(3))));;
gap> DrawOrbitPicture(G,[0,1],13,256,256,true,
>                     [[255,0,0],[0,255,0],[0,0,255]],
>                     Filename(dir,"example4.bmp"));
gap> G := Group(ClassShift(0,1),ClassTransposition(1,2,0,4));;
gap> DrawOrbitPicture(G,[0,1],20,512,512,true,
>                     List([1..20],i->[255-12*i,255-12*i,255]),
>                     Filename(dir,"example5.bmp"));
gap> G := Group(mKnot(3),ClassShift(Integers));;
gap> palette := [[255,  0,  0],[  0,255,  0],[  0,  0,255],
>                [255,255,  0],[255,  0,255],[  0,255,255],
>                [255,128,  0],[255,  0,128],[128,255,  0],
>                [  0,255,128],[128,  0,255],[  0,128,255]];;
gap> DrawOrbitPicture(G,[0,1],16,512,512,true,palette,
>                     Filename(dir,"example6.bmp"));
gap> G := Group(ClassTransposition(0,2,1,2),
>               ClassShift(0,4))^ClassTransposition(0,2,1,4);;
gap> DrawOrbitPicture(G,[0,1],30,512,512,false,fail,
>                     Filename(dir,"example7.bmp"));
gap> G := Group(ClassShift(0,2),
>               ClassTransposition(0,4,1,4))^ClassTransposition(1,2,0,6);;
gap> DrawOrbitPicture(G,[0,1],40,512,512,false,fail,
>                     Filename(dir,"example8.bmp"));
gap> examples := List([1..8],i->LoadBitmapPicture(Filename(dir,
>                     Concatenation("example",String(i),".bmp"))));;
gap> for i in [1..8] do
>      SaveAsBitmapPicture(examples[i],
>                          Filename(dir,Concatenation("example",String(i),
>                                                     "_copy.bmp")));
>    od;
gap> RCWADoThingsToBeDoneAfterTest();
gap> STOP_TEST( "picture.tst", 2400000000 );

#############################################################################
##
#E  picture.tst . . . . . . . . . . . . . . . . . . . . . . . . . . ends here
