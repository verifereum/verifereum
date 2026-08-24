Theory vfmTest0487[no_sig_docs]
Ancestors vfmTestDefs0487
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0487_0.nsv", "result0487_1.nsv", "result0487_2.nsv", "result0487_3.nsv"];
val thyn = "vfmTestDefs0487";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
