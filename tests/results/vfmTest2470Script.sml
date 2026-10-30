Theory vfmTest2470[no_sig_docs]
Ancestors vfmTestDefs2470
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2470_0.nsv", "result2470_1.nsv", "result2470_2.nsv", "result2470_3.nsv", "result2470_4.nsv", "result2470_5.nsv", "result2470_6.nsv", "result2470_7.nsv"];
val thyn = "vfmTestDefs2470";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
