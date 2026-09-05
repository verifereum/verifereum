Theory vfmTest2310[no_sig_docs]
Ancestors vfmTestDefs2310
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2310_0.nsv", "result2310_1.nsv", "result2310_2.nsv", "result2310_3.nsv", "result2310_4.nsv", "result2310_5.nsv", "result2310_6.nsv", "result2310_7.nsv"];
val thyn = "vfmTestDefs2310";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
