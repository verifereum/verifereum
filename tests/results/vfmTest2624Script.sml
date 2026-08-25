Theory vfmTest2624[no_sig_docs]
Ancestors vfmTestDefs2624
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2624_0.nsv", "result2624_1.nsv", "result2624_2.nsv", "result2624_3.nsv"];
val thyn = "vfmTestDefs2624";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
