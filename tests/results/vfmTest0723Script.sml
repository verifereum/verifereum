Theory vfmTest0723[no_sig_docs]
Ancestors vfmTestDefs0723
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0723_0.nsv", "result0723_1.nsv", "result0723_2.nsv", "result0723_3.nsv", "result0723_4.nsv", "result0723_5.nsv", "result0723_6.nsv", "result0723_7.nsv", "result0723_8.nsv", "result0723_9.nsv"];
val thyn = "vfmTestDefs0723";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
