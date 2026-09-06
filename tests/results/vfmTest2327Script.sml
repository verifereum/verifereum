Theory vfmTest2327[no_sig_docs]
Ancestors vfmTestDefs2327
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2327_0.nsv", "result2327_1.nsv", "result2327_2.nsv", "result2327_3.nsv", "result2327_4.nsv", "result2327_5.nsv", "result2327_6.nsv", "result2327_7.nsv", "result2327_8.nsv"];
val thyn = "vfmTestDefs2327";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
