Theory vfmTest0015[no_sig_docs]
Ancestors vfmTestDefs0015
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0015_0.nsv", "result0015_1.nsv", "result0015_2.nsv", "result0015_3.nsv", "result0015_4.nsv", "result0015_5.nsv", "result0015_6.nsv", "result0015_7.nsv", "result0015_8.nsv", "result0015_9.nsv"];
val thyn = "vfmTestDefs0015";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
