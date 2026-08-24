Theory vfmTest2625[no_sig_docs]
Ancestors vfmTestDefs2625
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2625_0.nsv", "result2625_1.nsv", "result2625_2.nsv", "result2625_3.nsv"];
val thyn = "vfmTestDefs2625";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
