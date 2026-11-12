Theory vfmTest0599[no_sig_docs]
Ancestors vfmTestDefs0599
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0599_0.nsv", "result0599_1.nsv", "result0599_2.nsv", "result0599_3.nsv", "result0599_4.nsv", "result0599_5.nsv", "result0599_6.nsv", "result0599_7.nsv", "result0599_8.nsv", "result0599_9.nsv"];
val thyn = "vfmTestDefs0599";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
