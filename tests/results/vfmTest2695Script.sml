Theory vfmTest2695[no_sig_docs]
Ancestors vfmTestDefs2695
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2695_0.nsv", "result2695_1.nsv", "result2695_2.nsv", "result2695_3.nsv"];
val thyn = "vfmTestDefs2695";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
