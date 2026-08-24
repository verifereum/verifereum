Theory vfmTest2790[no_sig_docs]
Ancestors vfmTestDefs2790
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2790_0.nsv", "result2790_1.nsv", "result2790_2.nsv", "result2790_3.nsv"];
val thyn = "vfmTestDefs2790";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
