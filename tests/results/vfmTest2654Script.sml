Theory vfmTest2654[no_sig_docs]
Ancestors vfmTestDefs2654
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2654_0.nsv", "result2654_1.nsv", "result2654_2.nsv", "result2654_3.nsv"];
val thyn = "vfmTestDefs2654";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
