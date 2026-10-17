Theory vfmTest0206[no_sig_docs]
Ancestors vfmTestDefs0206
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0206_0.nsv", "result0206_1.nsv", "result0206_2.nsv", "result0206_3.nsv", "result0206_4.nsv", "result0206_5.nsv", "result0206_6.nsv", "result0206_7.nsv", "result0206_8.nsv", "result0206_9.nsv"];
val thyn = "vfmTestDefs0206";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
