Theory vfmTest2657[no_sig_docs]
Ancestors vfmTestDefs2657
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2657_0.nsv", "result2657_1.nsv", "result2657_2.nsv", "result2657_3.nsv"];
val thyn = "vfmTestDefs2657";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
