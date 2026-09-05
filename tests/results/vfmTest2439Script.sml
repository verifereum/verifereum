Theory vfmTest2439[no_sig_docs]
Ancestors vfmTestDefs2439
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2439_0.nsv", "result2439_1.nsv", "result2439_2.nsv", "result2439_3.nsv", "result2439_4.nsv", "result2439_5.nsv", "result2439_6.nsv", "result2439_7.nsv"];
val thyn = "vfmTestDefs2439";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
