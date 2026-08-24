Theory vfmTest2698[no_sig_docs]
Ancestors vfmTestDefs2698
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2698_0.nsv", "result2698_1.nsv", "result2698_2.nsv", "result2698_3.nsv"];
val thyn = "vfmTestDefs2698";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
