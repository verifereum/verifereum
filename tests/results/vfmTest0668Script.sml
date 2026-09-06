Theory vfmTest0668[no_sig_docs]
Ancestors vfmTestDefs0668
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0668_0.nsv", "result0668_1.nsv", "result0668_2.nsv", "result0668_3.nsv", "result0668_4.nsv", "result0668_5.nsv", "result0668_6.nsv", "result0668_7.nsv", "result0668_8.nsv", "result0668_9.nsv"];
val thyn = "vfmTestDefs0668";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
