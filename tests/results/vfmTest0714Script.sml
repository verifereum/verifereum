Theory vfmTest0714[no_sig_docs]
Ancestors vfmTestDefs0714
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0714_0.nsv", "result0714_1.nsv", "result0714_2.nsv", "result0714_3.nsv", "result0714_4.nsv", "result0714_5.nsv", "result0714_6.nsv", "result0714_7.nsv", "result0714_8.nsv", "result0714_9.nsv"];
val thyn = "vfmTestDefs0714";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
