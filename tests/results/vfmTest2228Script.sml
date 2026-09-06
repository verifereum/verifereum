Theory vfmTest2228[no_sig_docs]
Ancestors vfmTestDefs2228
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2228_0.nsv", "result2228_1.nsv", "result2228_2.nsv", "result2228_3.nsv", "result2228_4.nsv", "result2228_5.nsv", "result2228_6.nsv", "result2228_7.nsv", "result2228_8.nsv"];
val thyn = "vfmTestDefs2228";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
