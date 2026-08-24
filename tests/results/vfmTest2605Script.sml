Theory vfmTest2605[no_sig_docs]
Ancestors vfmTestDefs2605
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2605_0.nsv", "result2605_1.nsv", "result2605_2.nsv", "result2605_3.nsv"];
val thyn = "vfmTestDefs2605";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
