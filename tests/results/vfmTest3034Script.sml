Theory vfmTest3034[no_sig_docs]
Ancestors vfmTestDefs3034
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3034_0.nsv", "result3034_1.nsv", "result3034_2.nsv", "result3034_3.nsv", "result3034_4.nsv", "result3034_5.nsv", "result3034_6.nsv", "result3034_7.nsv", "result3034_8.nsv"];
val thyn = "vfmTestDefs3034";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
