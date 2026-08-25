Theory vfmTest0474[no_sig_docs]
Ancestors vfmTestDefs0474
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0474_0.nsv", "result0474_1.nsv", "result0474_2.nsv", "result0474_3.nsv", "result0474_4.nsv", "result0474_5.nsv", "result0474_6.nsv", "result0474_7.nsv", "result0474_8.nsv", "result0474_9.nsv"];
val thyn = "vfmTestDefs0474";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
