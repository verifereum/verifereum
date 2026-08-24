Theory vfmTest2645[no_sig_docs]
Ancestors vfmTestDefs2645
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2645_0.nsv", "result2645_1.nsv", "result2645_2.nsv", "result2645_3.nsv"];
val thyn = "vfmTestDefs2645";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
