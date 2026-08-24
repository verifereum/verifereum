Theory vfmTest2824[no_sig_docs]
Ancestors vfmTestDefs2824
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2824_0.nsv", "result2824_1.nsv", "result2824_2.nsv", "result2824_3.nsv"];
val thyn = "vfmTestDefs2824";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
