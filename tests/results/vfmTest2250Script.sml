Theory vfmTest2250[no_sig_docs]
Ancestors vfmTestDefs2250
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2250_0.nsv", "result2250_1.nsv", "result2250_2.nsv", "result2250_3.nsv", "result2250_4.nsv", "result2250_5.nsv"];
val thyn = "vfmTestDefs2250";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
