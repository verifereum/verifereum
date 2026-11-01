Theory vfmTest0626[no_sig_docs]
Ancestors vfmTestDefs0626
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0626_0.nsv", "result0626_1.nsv", "result0626_2.nsv", "result0626_3.nsv", "result0626_4.nsv", "result0626_5.nsv", "result0626_6.nsv", "result0626_7.nsv", "result0626_8.nsv", "result0626_9.nsv"];
val thyn = "vfmTestDefs0626";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
