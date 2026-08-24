Theory vfmTest2749[no_sig_docs]
Ancestors vfmTestDefs2749
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2749_0.nsv", "result2749_1.nsv", "result2749_2.nsv", "result2749_3.nsv"];
val thyn = "vfmTestDefs2749";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
