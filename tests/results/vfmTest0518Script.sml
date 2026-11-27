Theory vfmTest0518[no_sig_docs]
Ancestors vfmTestDefs0518
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0518_0.nsv", "result0518_1.nsv", "result0518_2.nsv", "result0518_3.nsv", "result0518_4.nsv", "result0518_5.nsv", "result0518_6.nsv", "result0518_7.nsv"];
val thyn = "vfmTestDefs0518";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
