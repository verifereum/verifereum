Theory vfmTest0130[no_sig_docs]
Ancestors vfmTestDefs0130
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0130_0.nsv", "result0130_1.nsv", "result0130_2.nsv", "result0130_3.nsv", "result0130_4.nsv", "result0130_5.nsv", "result0130_6.nsv", "result0130_7.nsv"];
val thyn = "vfmTestDefs0130";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
