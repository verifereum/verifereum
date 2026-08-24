Theory vfmTest2700[no_sig_docs]
Ancestors vfmTestDefs2700
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2700_0.nsv", "result2700_1.nsv", "result2700_2.nsv", "result2700_3.nsv"];
val thyn = "vfmTestDefs2700";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
