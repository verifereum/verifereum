Theory vfmTest2440[no_sig_docs]
Ancestors vfmTestDefs2440
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2440_0.nsv", "result2440_1.nsv", "result2440_2.nsv", "result2440_3.nsv", "result2440_4.nsv", "result2440_5.nsv", "result2440_6.nsv", "result2440_7.nsv"];
val thyn = "vfmTestDefs2440";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
