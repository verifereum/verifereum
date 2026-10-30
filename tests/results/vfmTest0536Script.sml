Theory vfmTest0536[no_sig_docs]
Ancestors vfmTestDefs0536
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0536_0.nsv", "result0536_1.nsv", "result0536_2.nsv", "result0536_3.nsv", "result0536_4.nsv", "result0536_5.nsv"];
val thyn = "vfmTestDefs0536";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
