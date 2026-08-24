Theory vfmTest2598[no_sig_docs]
Ancestors vfmTestDefs2598
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2598_0.nsv", "result2598_1.nsv", "result2598_2.nsv", "result2598_3.nsv"];
val thyn = "vfmTestDefs2598";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
