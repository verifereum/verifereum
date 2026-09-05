Theory vfmTest2387[no_sig_docs]
Ancestors vfmTestDefs2387
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2387_0.nsv", "result2387_1.nsv", "result2387_2.nsv", "result2387_3.nsv", "result2387_4.nsv", "result2387_5.nsv", "result2387_6.nsv", "result2387_7.nsv", "result2387_8.nsv", "result2387_9.nsv"];
val thyn = "vfmTestDefs2387";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
