Theory vfmTest0383[no_sig_docs]
Ancestors vfmTestDefs0383
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0383_0.nsv", "result0383_1.nsv", "result0383_2.nsv", "result0383_3.nsv", "result0383_4.nsv", "result0383_5.nsv", "result0383_6.nsv", "result0383_7.nsv"];
val thyn = "vfmTestDefs0383";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
