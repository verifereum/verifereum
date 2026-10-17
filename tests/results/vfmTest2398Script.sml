Theory vfmTest2398[no_sig_docs]
Ancestors vfmTestDefs2398
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2398_0.nsv", "result2398_1.nsv", "result2398_2.nsv", "result2398_3.nsv", "result2398_4.nsv", "result2398_5.nsv", "result2398_6.nsv", "result2398_7.nsv", "result2398_8.nsv", "result2398_9.nsv", "result2398_10.nsv", "result2398_11.nsv"];
val thyn = "vfmTestDefs2398";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
