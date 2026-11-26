Theory vfmTest2171[no_sig_docs]
Ancestors vfmTestDefs2171
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2171_0.nsv", "result2171_1.nsv", "result2171_2.nsv", "result2171_3.nsv", "result2171_4.nsv", "result2171_5.nsv", "result2171_6.nsv", "result2171_7.nsv"];
val thyn = "vfmTestDefs2171";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
