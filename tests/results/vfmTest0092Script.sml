Theory vfmTest0092[no_sig_docs]
Ancestors vfmTestDefs0092
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0092_0.nsv", "result0092_1.nsv", "result0092_2.nsv", "result0092_3.nsv", "result0092_4.nsv", "result0092_5.nsv", "result0092_6.nsv", "result0092_7.nsv"];
val thyn = "vfmTestDefs0092";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
