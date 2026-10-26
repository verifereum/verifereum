Theory vfmTest0729[no_sig_docs]
Ancestors vfmTestDefs0729
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0729_0.nsv", "result0729_1.nsv", "result0729_2.nsv", "result0729_3.nsv", "result0729_4.nsv", "result0729_5.nsv", "result0729_6.nsv", "result0729_7.nsv"];
val thyn = "vfmTestDefs0729";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
