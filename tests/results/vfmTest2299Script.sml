Theory vfmTest2299[no_sig_docs]
Ancestors vfmTestDefs2299
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2299_0.nsv", "result2299_1.nsv", "result2299_2.nsv", "result2299_3.nsv", "result2299_4.nsv", "result2299_5.nsv", "result2299_6.nsv", "result2299_7.nsv"];
val thyn = "vfmTestDefs2299";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
