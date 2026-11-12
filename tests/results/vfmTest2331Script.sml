Theory vfmTest2331[no_sig_docs]
Ancestors vfmTestDefs2331
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2331_0.nsv", "result2331_1.nsv", "result2331_2.nsv", "result2331_3.nsv", "result2331_4.nsv", "result2331_5.nsv", "result2331_6.nsv", "result2331_7.nsv"];
val thyn = "vfmTestDefs2331";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
