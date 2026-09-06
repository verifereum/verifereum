Theory vfmTest0059[no_sig_docs]
Ancestors vfmTestDefs0059
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0059_0.nsv", "result0059_1.nsv", "result0059_2.nsv", "result0059_3.nsv", "result0059_4.nsv", "result0059_5.nsv", "result0059_6.nsv", "result0059_7.nsv", "result0059_8.nsv", "result0059_9.nsv"];
val thyn = "vfmTestDefs0059";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
