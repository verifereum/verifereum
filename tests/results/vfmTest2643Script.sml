Theory vfmTest2643[no_sig_docs]
Ancestors vfmTestDefs2643
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2643_0.nsv", "result2643_1.nsv", "result2643_2.nsv", "result2643_3.nsv"];
val thyn = "vfmTestDefs2643";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
