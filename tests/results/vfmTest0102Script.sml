Theory vfmTest0102[no_sig_docs]
Ancestors vfmTestDefs0102
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0102_0.nsv", "result0102_1.nsv", "result0102_2.nsv", "result0102_3.nsv"];
val thyn = "vfmTestDefs0102";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
