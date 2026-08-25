Theory vfmTest0964[no_sig_docs]
Ancestors vfmTestDefs0964
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0964_0.nsv", "result0964_1.nsv", "result0964_2.nsv", "result0964_3.nsv", "result0964_4.nsv", "result0964_5.nsv", "result0964_6.nsv", "result0964_7.nsv"];
val thyn = "vfmTestDefs0964";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
